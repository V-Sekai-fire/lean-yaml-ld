import Lean.Data.Json
import JsonLd.Iri

/-! A JSON-LD 1.1 processor: context processing (API 4.1, 4.2), IRI expansion (5.2), the expansion algorithm (5.1) and value expansion (5.3).
Errors are the error codes of the JSON-LD API, as strings (`invalid @context entry`, ...). -/

namespace JsonLd
open Lean

/-! ## Json helpers -/

def entries (j : Json) : List (String × Json) :=
  match j with
  | .obj o => o.toList
  | _ => []

def isMap : Json → Bool
  | .obj _ => true
  | _ => false

def isArr : Json → Bool
  | .arr _ => true
  | _ => false

def isStr : Json → Bool
  | .str _ => true
  | _ => false

def isScalar : Json → Bool
  | .str _ | .num _ | .bool _ => true
  | _ => false

def arrayify : Json → List Json
  | .arr a => a.toList
  | j => [j]

def get? (j : Json) (k : String) : Option Json := (j.getObjVal? k).toOption

def has (j : Json) (k : String) : Bool := (get? j k).isSome

def setKey (j : Json) (k : String) (v : Json) : Json :=
  Json.mkObj ((entries j).filter (·.1 != k) ++ [(k, v)])

def delKey (j : Json) (k : String) : Json := Json.mkObj ((entries j).filter (·.1 != k))

def keysOf (j : Json) : List String := (entries j).map (·.1)

/-- Add a value under a key of a map, as an array entry (`add value`). -/
def addTo (j : Json) (k : String) (vs : List Json) : Json :=
  let old := match get? j k with | some (.arr a) => a.toList | some x => [x] | none => []
  setKey j k (Json.arr (old ++ vs).toArray)

def sortStrings (l : List String) : List String := (l.toArray.qsort (· < ·)).toList

def sortEntries (l : List (String × Json)) : List (String × Json) := (l.toArray.qsort (fun a b => a.1 < b.1)).toList

def asStr? : Json → Option String
  | .str s => some s
  | _ => none

/-! ## Contexts -/

structure TermDef where
  iri : Option String := none
  reverse : Bool := false
  isPrefix : Bool := false
  isProtected : Bool := false
  typeMapping : Option String := none
  languageMapping : Option (Option String) := none
  directionMapping : Option (Option String) := none
  container : List String := []
  indexMapping : Option String := none
  nestValue : Option String := none
  localContext : Option Json := none
  baseUrl : Option String := none
  deriving BEq, Inhabited

structure Context where
  defs : List (String × TermDef) := []
  base : Option String := none
  originalBase : Option String := none
  vocab : Option String := none
  language : Option String := none
  direction : Option String := none
  previous : Option Context := none

instance : Inhabited Context := ⟨{}⟩

def Context.find (c : Context) (t : String) : Option TermDef := c.defs.lookup t

def Context.set (c : Context) (t : String) (d : TermDef) : Context :=
  { c with defs := (t, d) :: c.defs.filter (·.1 != t) }

def Context.erase (c : Context) (t : String) : Context := { c with defs := c.defs.filter (·.1 != t) }

structure Cfg where
  loader : String → IO (Except String Json)
  /-- `json-ld-1.0` is refused: this processor is 1.1 only. -/
  mode10 : Bool := false
  /-- YAML-LD overrides JSON-LD: a context document at one of these URLs may be a bare context, with no `@context` entry. -/
  bareContext : String → Bool := fun _ => false

abbrev PM := ReaderT Cfg (ExceptT String IO)

instance : Inhabited (PM α) := ⟨throw "unreachable"⟩

def fail (code : String) : PM α := throw code

def loadRemote (url : String) : PM Json := do
  let cfg ← read
  match ← (cfg.loader url : IO _) with
  | .ok j => pure j
  | .error _ => fail "loading remote context failed"

def hasColonAfterFirst (s : String) : Bool := (s.toList.drop 1).contains ':'

def validContainer (cs : List String) : Bool :=
  let allowed := ["@graph", "@id", "@index", "@language", "@list", "@set", "@type"]
  let noSet := cs.filter (· != "@set")
  let sorted := sortStrings noSet
  cs.all allowed.contains && cs.eraseDups.length == cs.length &&
  (sorted == [] || sorted == ["@graph"] || sorted == ["@graph", "@id"] || sorted == ["@graph", "@index"] ||
   sorted == ["@id"] || sorted == ["@index"] || sorted == ["@language"] || sorted == ["@type"] ||
   (sorted == ["@list"] && cs.length == 1))

def isBlank (s : String) : Bool := isBlankNode s

/-- A defined-map: terms being defined (false) or defined (true). -/
abbrev Defined := IO.Ref (List (String × Bool))

mutual

/-- IRI expansion (5.2). -/
partial def expandIri (ac0 : Context) (value : String) (documentRelative vocab : Bool)
    (loc : Option (Json × Defined × IO.Ref Context × Option String) := none) : PM (Option String) := do
  if isKeyword value then return some value
  if keywordLike value then return none
  if let some (lc, defd, rc, cb) := loc then
    if has lc value then
      let st ← defd.get
      if st.lookup value != some true then createTerm rc lc value defd false false [] false cb
  let ac ← match loc with | some (_, _, rc, _) => rc.get | none => pure ac0
  match ac.find value with
  | some d =>
    match d.iri with
    | some i => if isKeyword i then return some i
    | none => pure ()
  | none => pure ()
  if vocab then
    if let some d := ac.find value then return d.iri
  if hasColonAfterFirst value then
    match splitFirst value ':' with
    | some (pre, suf) =>
      if pre == "_" || suf.startsWith "//" then return some value
      if let some (lc, defd, rc, cb) := loc then
        if has lc pre then
          let st ← defd.get
          if st.lookup pre != some true then createTerm rc lc pre defd false false [] false cb
      let ac ← match loc with | some (_, _, rc, _) => rc.get | none => pure ac0
      match ac.find pre with
      | some d =>
        match d.iri with
        | some i => if d.isPrefix then return some (i ++ suf)
        | none => pure ()
      | none => pure ()
      if isAbsoluteIri value then return some value
    | none => pure ()
  if vocab then
    if let some v := ac.vocab then return some (v ++ value)
  if documentRelative then
    match ac.base with
    | some b => return some (resolveIri b value)
    | none => pure ()
  return some value

/-- Create a term definition (4.2), in the context held by `rc`. `lc` is the lctx0 context, `defd` the terms done or in progress. -/
partial def createTerm (rc : IO.Ref Context) (lc : Json) (term : String) (defd : Defined)
    (prot overrideProt : Bool) (remote : List String) (validate : Bool) (cb : Option String) : PM Unit := do
  let st ← defd.get
  match st.lookup term with
  | some true => return
  | some false => fail "cyclic IRI mapping"
  | none => pure ()
  if term == "" then fail "invalid term definition"
  if (match get? lc term with | some (.obj _ ) => has (get? lc term |>.getD Json.null) "@prefix" | _ => false) && (term.contains ':' || term.contains '/') then
    fail "invalid term definition"
  let markDone : PM Unit := defd.modify fun l => (term, true) :: l.filter (·.1 != term)
  defd.modify fun l => (term, false) :: l.filter (·.1 != term)
  let some value := get? lc term | markDone
  let cfg ← read
  let loc : Option (Json × Defined × IO.Ref Context × Option String) := some (lc, defd, rc, cb)
  let exp (s : String) (docRel vocab : Bool) : PM (Option String) := do expandIri (← rc.get) s docRel vocab loc
  if term == "@type" then
    match value with
    | .obj _ =>
      let ks := keysOf value
      let okKeys := ks.all (fun k => k == "@container" || k == "@protected")
      if !okKeys || ks.isEmpty || (has value "@container" && get? value "@container" != some (Json.str "@set")) then fail "keyword redefinition"
    | _ => fail "keyword redefinition"
  else if isKeyword term then fail "keyword redefinition"
  else if keywordLike term then
    markDone
    return
  let previous := (← rc.get).find term
  rc.modify (·.erase term)
  let simple : Bool := isStr value
  let v : Json ← match value with
    | .null => pure (Json.mkObj [("@id", Json.null)])
    | .str _ => pure (Json.mkObj [("@id", value)])
    | .obj _ => pure value
    | _ => fail "invalid term definition"
  let mut d : TermDef := { isProtected := prot }
  match get? v "@protected" with
  | some (.bool b) => d := { d with isProtected := b }
  | some _ => fail "invalid @protected value"
  | none => pure ()
  if let some t := get? v "@type" then
    let .str ts := t | fail "invalid type mapping"
    match ← exp ts false true with
    | some x =>
      if x == "@id" || x == "@vocab" || x == "@json" || x == "@none" || (isAbsoluteIri x && !isKeyword x) then
        if (x == "@json" || x == "@none") && cfg.mode10 then fail "invalid type mapping"
        d := { d with typeMapping := some x }
      else fail "invalid type mapping"
    | none => fail "invalid type mapping"
  if let some rv := get? v "@reverse" then
    if has v "@id" || has v "@nest" then fail "invalid reverse property"
    let .str rs := rv | fail "invalid IRI mapping"
    if keywordLike rs && !isKeyword rs then
      markDone
      return
    match ← exp rs false true with
    | some x => if (isAbsoluteIri x || isBlank x) then d := { d with iri := some x } else fail "invalid IRI mapping"
    | none => fail "invalid IRI mapping"
    match get? v "@container" with
    | none | some .null => pure ()
    | some (.str "@set") => d := { d with container := ["@set"] }
    | some (.str "@index") => d := { d with container := ["@index"] }
    | some _ => fail "invalid reverse property"
    if let some (.str xs) := get? v "@index" then
      if d.container.contains "@index" then d := { d with indexMapping := some xs }
    d := { d with reverse := true, baseUrl := cb }
    rc.modify (·.set term d)
    markDone
    return
  let mut idDone := false
  if let some idv := get? v "@id" then
    if idv != Json.str term then
      match idv with
      | .null => idDone := true
      | .str is =>
        if !isKeyword is && keywordLike is then
          markDone
          return
        match ← exp is false true with
        | some x =>
          if !(isKeyword x || isAbsoluteIri x || isBlank x) then fail "invalid IRI mapping"
          if x == "@context" then fail "invalid keyword alias"
          d := { d with iri := some x }
          idDone := true
          if (term.toList.dropLast.contains ':') || term.contains '/' then
            markDone
            if (← exp term false true) != some x then fail "invalid IRI mapping"
          if !term.contains ':' && !term.contains '/' && simple &&
              (isBlank x || (x.toList.getLast?.any fun c => ":/?#[]@".toList.contains c)) then
            d := { d with isPrefix := true }
        | none => fail "invalid IRI mapping"
      | _ => fail "invalid IRI mapping"
  if !idDone then
    if hasColonAfterFirst term then
      match splitFirst term ':' with
      | some (pre, suf) =>
        if has lc pre then createTerm rc lc pre defd false false [] false cb
        match (← rc.get).find pre with
        | some pd =>
          match pd.iri with
          | some pi => d := { d with iri := some (pi ++ suf) }
          | none => if isAbsoluteIri term || isBlank term then d := { d with iri := some term }
        | none => if isAbsoluteIri term || isBlank term then d := { d with iri := some term }
      | none => pure ()
    else if term.contains '/' then
      match ← expandIri (← rc.get) term false true with
      | some x => if isAbsoluteIri x || isBlank x then d := { d with iri := some x } else fail "invalid IRI mapping"
      | none => fail "invalid IRI mapping"
    else if term == "@type" then d := { d with iri := some "@type" }
    else
      match (← rc.get).vocab with
      | some vm => d := { d with iri := some (vm ++ term) }
      | none => fail "invalid IRI mapping"
  if let some c := get? v "@container" then
    let cs : List String ← match c with
      | .str s => pure [s]
      | .arr a => a.toList.mapM fun x => match x with | .str s => pure s | _ => fail "invalid container mapping"
      | _ => fail "invalid container mapping"
    if !validContainer cs then fail "invalid container mapping"
    if cs.contains "@type" then
      match d.typeMapping with
      | none => d := { d with typeMapping := some "@id" }
      | some "@id" | some "@vocab" => pure ()
      | some _ => fail "invalid type mapping"
    d := { d with container := cs }
  if let some ix := get? v "@index" then
    if !d.container.contains "@index" then fail "invalid term definition"
    let .str xs := ix | fail "invalid term definition"
    match ← exp xs false true with
    | some x => if isAbsoluteIri x then d := { d with indexMapping := some xs } else fail "invalid term definition"
    | none => fail "invalid term definition"
  if let some cx := get? v "@context" then
    try
      let _ ← processContext (← rc.get) cx cb remote true true false
    catch _ => fail "invalid scoped context"
    d := { d with localContext := some cx }
  d := { d with baseUrl := cb }
  if !has v "@type" then
    match get? v "@language" with
    | some .null => d := { d with languageMapping := some none }
    | some (.str l) => d := { d with languageMapping := some (some l) }
    | some _ => fail "invalid language mapping"
    | none => pure ()
  match get? v "@direction" with
  | some .null => d := { d with directionMapping := some none }
  | some (.str "ltr") => d := { d with directionMapping := some (some "ltr") }
  | some (.str "rtl") => d := { d with directionMapping := some (some "rtl") }
  | some _ => fail "invalid base direction"
  | none => pure ()
  if let some n := get? v "@nest" then
    let .str ns := n | fail "invalid @nest value"
    if isKeyword ns && ns != "@nest" then fail "invalid @nest value"
    d := { d with nestValue := some ns }
  if let some pv := get? v "@prefix" then
    if term.contains ':' || term.contains '/' then fail "invalid term definition"
    match pv with
    | .bool b =>
      if b && d.iri.any isKeyword then fail "invalid term definition"
      d := { d with isPrefix := b }
    | _ => fail "invalid @prefix value"
  let allowed := ["@id", "@reverse", "@container", "@context", "@direction", "@index", "@language", "@nest", "@prefix", "@protected", "@type"]
  if !(keysOf v).all allowed.contains then fail "invalid term definition"
  if !overrideProt then
    if let some pd := previous then
      if pd.isProtected then
        if { pd with isProtected := false } != { d with isProtected := false } then fail "protected term redefinition"
        d := pd
  rc.modify (·.set term d)
  markDone

/-- Context processing (4.1). -/
partial def processContext (active : Context) (lctx0 : Json) (baseUrl : Option String) (remote : List String)
    (overrideProt : Bool) (propagate0 validateScoped : Bool) : PM Context := do
  let cfg ← read
  let mut result := active
  let mut propagate := propagate0
  if let some p := get? lctx0 "@propagate" then
    match p with
    | .bool b => propagate := b
    | _ => fail "invalid @propagate value"
  if !propagate && result.previous.isNone then result := { result with previous := some active }
  for ctx in arrayify lctx0 do
    match ctx with
    | .null =>
      if !overrideProt && result.defs.any (·.2.isProtected) then fail "invalid context nullification"
      let prev := result
      result := { ({} : Context) with base := active.originalBase, originalBase := active.originalBase }
      if !propagate then result := { result with previous := some prev }
    | .str s =>
      let url := match baseUrl with | some b => resolveIri b s | none => s
      if !validateScoped && remote.contains url then continue
      if remote.length > 256 then fail "context overflow"
      let doc ← loadRemote url
      if !isMap doc then fail "invalid remote context"
      let inner ← match get? doc "@context" with
        | some i => pure i
        | none => if cfg.bareContext url then pure doc else fail "invalid remote context"
      result ← processContext result inner (some url) (url :: remote) overrideProt true false
    | .obj _ =>
      let mut c := ctx
      if let some ver := get? c "@version" then
        match ver with
        | .num n => if n.toString != "1.1" && n.toString != "1.1e0" then fail "invalid @version value"
        | _ => fail "invalid @version value"
        if cfg.mode10 then fail "processing mode conflict"
      if let some imp := get? c "@import" then
        if cfg.mode10 then fail "invalid context entry"
        let .str is := imp | fail "invalid @import value"
        let url := match baseUrl with | some b => resolveIri b is | none => is
        let doc ← loadRemote url
        match get? doc "@context" with
        | some ic@(.obj _) =>
          if has ic "@import" then fail "invalid context entry"
          c := Json.mkObj ((entries ic).filter (fun e => !has c e.1) ++ (entries c).filter (·.1 != "@import"))
        | _ => fail "invalid remote context"
      if remote.isEmpty then
        match get? c "@base" with
        | some .null => result := { result with base := none }
        | some (.str b) =>
          if isAbsoluteIri b then result := { result with base := some b }
          else match result.base with
            | some cur => result := { result with base := some (resolveIri cur b) }
            | none => fail "invalid base IRI"
        | some _ => fail "invalid base IRI"
        | none => pure ()
      match get? c "@vocab" with
      | some .null => result := { result with vocab := none }
      | some (.str vs) =>
        match ← expandIri result vs true true with
        | some x => if isAbsoluteIri x || isBlank x || isKeyword x then result := { result with vocab := some x } else fail "invalid vocab mapping"
        | none => fail "invalid vocab mapping"
      | some _ => fail "invalid vocab mapping"
      | none => pure ()
      match get? c "@language" with
      | some .null => result := { result with language := none }
      | some (.str l) => result := { result with language := some l }
      | some _ => fail "invalid default language"
      | none => pure ()
      match get? c "@direction" with
      | some .null => result := { result with direction := none }
      | some (.str "ltr") => result := { result with direction := some "ltr" }
      | some (.str "rtl") => result := { result with direction := some "rtl" }
      | some _ => fail "invalid base direction"
      | none => pure ()
      if has c "@propagate" && cfg.mode10 then fail "invalid context entry"
      let prot ← match get? c "@protected" with
        | some (.bool b) => pure b
        | some _ => fail "invalid @protected value"
        | none => pure false
      let defd ← (IO.mkRef ([] : List (String × Bool)) : IO _)
      let rc ← (IO.mkRef result : IO _)
      let skip := ["@base", "@direction", "@import", "@language", "@propagate", "@protected", "@version", "@vocab"]
      for (k, _) in entries c do
        if !skip.contains k then createTerm rc c k defd prot overrideProt remote false baseUrl
      result ← rc.get
    | _ => fail "invalid local context"
  return result

end

/-! ## Expansion -/

structure ExpOpts where
  frame : Bool := false
  /-- YAML-LD overrides JSON-LD: a top-level node whose properties were all null, leaving only an `@id`, is kept. -/
  keepIdOnly : Bool := false

def isValueObj (j : Json) : Bool := isMap j && has j "@value"
def isListObj (j : Json) : Bool := isMap j && has j "@list"
def isGraphObj (j : Json) : Bool :=
  isMap j && has j "@graph" && (keysOf j).all (fun k => k == "@graph" || k == "@id" || k == "@index" || k == "@context")
def isNodeObj (j : Json) : Bool := isMap j && !has j "@value" && !has j "@list" && !has j "@set"

/-- Value expansion (5.3). -/
def expandValue (ac : Context) (prop : String) (v : Json) : PM Json := do
  let d := ac.find prop
  match v, d.bind (·.typeMapping) with
  | .str s, some "@id" =>
    match ← expandIri ac s true false with
    | some x => return Json.mkObj [("@id", Json.str x)]
    | none => return Json.mkObj [("@id", Json.null)]
  | .str s, some "@vocab" =>
    match ← expandIri ac s true true with
    | some x => return Json.mkObj [("@id", Json.str x)]
    | none => return Json.mkObj [("@id", Json.null)]
  | _, ty =>
    let mut r := Json.mkObj [("@value", v)]
    match ty with
    | some t => if t != "@id" && t != "@vocab" && t != "@none" then r := setKey r "@type" (Json.str t)
    | none =>
      if isStr v then
        let lang : Option String := match d.bind (·.languageMapping) with | some l => l | none => ac.language
        let dir : Option String := match d.bind (·.directionMapping) with | some l => l | none => ac.direction
        if let some l := lang then r := setKey r "@language" (Json.str l)
        if let some x := dir then r := setKey r "@direction" (Json.str x)
    return r

mutual

partial def expandElement (ac0 : Context) (activeProp : Option String) (element : Json) (baseUrl : Option String)
    (opts : ExpOpts) (fromMap : Bool) : PM (Option Json) := do
  let propDef := activeProp.bind ac0.find
  if propDef.any (·.typeMapping == some "@json") then
    return some (Json.mkObj [("@value", element), ("@type", Json.str "@json")])
  match element with
  | .null => return none
  | .arr items =>
    let mut res : Array Json := #[]
    for item in items do
      match ← expandElement ac0 activeProp item baseUrl opts fromMap with
      | none => pure ()
      | some e =>
        let listProp := propDef.any (·.container.contains "@list") || activeProp == some "@list"
        let e := if listProp && isArr e then Json.mkObj [("@list", e)] else e
        match e with
        | .arr a => res := res ++ a
        | _ => res := res.push e
    return some (Json.arr res)
  | .obj _ =>
    let mut ac := ac0
    if let some prev := ac.previous then
      if !fromMap then
        let mut hasValue := false
        for (k, _) in entries element do
          if (← expandIri ac k false true) == some "@value" then hasValue := true
        let single ← match entries element with
          | [(k, _)] => pure ((← expandIri ac k false true) == some "@id")
          | _ => pure false
        if !hasValue && !single then ac := prev
    if let some pd := propDef then
      if let some pc := pd.localContext then ac ← processContext ac pc pd.baseUrl [] true true false
    if let some cx := get? element "@context" then ac ← processContext ac cx baseUrl [] false true false
    let typeScoped := ac
    let mut inputType : Option String := none
    let mut firstType := true
    for (k, v) in entries element do
      if (← expandIri ac k false true) == some "@type" then
        let ts := (arrayify v).filterMap asStr?
        for t in sortStrings ts do
          if let some td := typeScoped.find t then
            if let some pc := td.localContext then ac ← processContext ac pc td.baseUrl [] false false false
        if firstType then
          firstType := false
          match (arrayify v).getLast? with
          | some (.str t) => inputType ← expandIri ac t false true
          | _ => pure ()
    let result ← (IO.mkRef (Json.mkObj []) : IO _)
    let nests ← (IO.mkRef ([] : List String) : IO _)
    expandEntries ac typeScoped activeProp element baseUrl opts inputType result nests
    let mut r ← result.get
    if opts.frame then
      if has r "@value" then
        match get? r "@type" with
        | some (.arr #[x@(.str _)]) => return some (setKey r "@type" x)
        | _ => pure ()
      return some r
    if has r "@value" then
      let ks := keysOf r
      if !ks.all (fun k => ["@direction", "@index", "@language", "@type", "@value"].contains k) then fail "invalid value object"
      if (has r "@language" || has r "@direction") && has r "@type" then fail "invalid value object"
      match get? r "@type" with
      | some (.arr #[x]) => r := setKey r "@type" x
      | some (.arr _) => fail "invalid typed value"
      | _ => pure ()
      if get? r "@type" == some (Json.str "@json") then pure ()
      else if get? r "@value" == some Json.null then return none
      else if has r "@language" && !(get? r "@value").any isStr then fail "invalid language-tagged value"
      else if let some t := get? r "@type" then
        match t with
        | .str ts => if !isAbsoluteIri ts then fail "invalid typed value"
        | _ => fail "invalid typed value"
    else if let some t := get? r "@type" then
      if !isArr t then r := setKey r "@type" (Json.arr #[t])
    else if has r "@set" || has r "@list" then
      if !(keysOf r).all (fun k => k == "@set" || k == "@list" || k == "@index") then fail "invalid set or list object"
      if let some sv := get? r "@set" then return some sv
    if keysOf r == ["@language"] then return none
    if activeProp.isNone || activeProp == some "@graph" then
      if (keysOf r).isEmpty || has r "@value" || has r "@list" then return none
      if keysOf r == ["@id"] && !opts.frame && !(opts.keepIdOnly && ((entries element).filter (·.1 != "@context")).length > 1) then return none
    return some r
  | _ =>
    if activeProp.isNone || activeProp == some "@graph" then return none
    let mut ac := ac0
    if let some pd := propDef then
      if let some pc := pd.localContext then ac ← processContext ac pc pd.baseUrl [] true true false
    return some (← expandValue ac activeProp.get! element)

partial def expandEntries (ac : Context) (typeScoped : Context) (activeProp : Option String) (elem : Json)
    (baseUrl : Option String) (opts : ExpOpts) (inputType : Option String)
    (result : IO.Ref Json) (nests : IO.Ref (List String)) : PM Unit := do
  for (key, value) in entries elem do
    if key == "@context" then continue
    let frameKws := ["@default", "@embed", "@explicit", "@omitDefault", "@requireAll"]
    let some ep ← (if opts.frame && frameKws.contains key then pure (some key) else expandIri ac key false true) | continue
    let frameKw := opts.frame && frameKws.contains ep
    if !ep.contains ':' && !isKeyword ep && !frameKw then continue
    if isKeyword ep || frameKw then
      if activeProp == some "@reverse" then fail "invalid reverse property map"
      let cur ← result.get
      if has cur ep && ep != "@included" && ep != "@type" then fail "colliding keywords"
      let put (v : Json) : PM Unit := result.modify fun r => setKey r ep v
      match ep with
      | "@id" =>
        match value with
        | .str s =>
          match ← expandIri ac s true false with
          | some x => put (Json.str x)
          | none => put Json.null
        | .obj _ => if opts.frame && (entries value).isEmpty then put (Json.arr #[value]) else fail "invalid @id value"
        | .arr a =>
          if opts.frame then
            let mut out : Array Json := #[]
            for x in a do
              match x with
              | .str s =>
                match ← expandIri ac s true false with
                | some y => out := out.push (Json.str y)
                | none => pure ()
              | .obj _ => if (entries x).isEmpty then out := out.push x else fail "invalid @id value"
              | _ => fail "invalid @id value"
            put (Json.arr out)
          else fail "invalid @id value"
        | _ => fail "invalid @id value"
      | "@type" =>
        let vs : List Json ← match value with
          | .str _ => pure [value]
          | .arr a => a.toList.mapM fun x => match x with | .str _ => pure x | .obj _ => (if opts.frame then pure x else fail "invalid type value") | _ => fail "invalid type value"
          | .obj _ => if opts.frame then pure [value] else fail "invalid type value"
          | _ => fail "invalid type value"
        let mut out : List Json := []
        for tj in vs do
          match tj with
          | .str t =>
            match ← expandIri typeScoped t true true with
            | some x => out := out ++ [Json.str x]
            | none => pure ()
          | _ =>
            -- a frame: the wildcard {}, or {"@default": type}
            match get? tj "@default" with
            | some (.str d) =>
              match ← expandIri typeScoped d true true with
              | some x => out := out ++ [Json.mkObj [("@default", Json.str x)]]
              | none => pure ()
            | _ => out := out ++ [tj]
        let old := match get? cur "@type" with | some (.arr a) => a.toList | some x => [x] | none => []
        put (Json.arr (old ++ out).toArray)
      | "@graph" =>
        let ev ← expandElement ac (some "@graph") value baseUrl opts false
        put (Json.arr ((arrayify (ev.getD Json.null)).filter (· != Json.null)).toArray)
      | "@included" =>
        let ev ← expandElement ac (some "@included") value baseUrl opts false
        let items := (arrayify (ev.getD Json.null)).filter (· != Json.null)
        if !items.all isNodeObj then fail "invalid @included value"
        let old := match get? cur "@included" with | some (.arr a) => a.toList | _ => []
        put (Json.arr (old ++ items).toArray)
      | "@value" =>
        if inputType == some "@json" then put value
        else
          match value with
          | .null => put Json.null
          | v => if isScalar v || opts.frame then put v else fail "invalid value object value"
      | "@language" =>
        match value with
        | .str l => put (Json.str l.toLower)
        | _ => if opts.frame then put value else fail "invalid language-tagged string"
      | "@direction" =>
        match value with
        | .str "ltr" | .str "rtl" => put value
        | _ => fail "invalid base direction"
      | "@index" =>
        match value with
        | .str _ => put value
        | _ => fail "invalid @index value"
      | "@list" =>
        if activeProp.isNone || activeProp == some "@graph" then continue
        let ev ← expandElement ac activeProp value baseUrl opts false
        put (Json.arr ((arrayify (ev.getD Json.null)).filter (· != Json.null)).toArray)
      | "@set" =>
        let ev ← expandElement ac activeProp value baseUrl opts false
        put (Json.arr ((arrayify (ev.getD Json.null)).filter (· != Json.null)).toArray)
      | "@reverse" =>
        if !isMap value then fail "invalid @reverse value"
        match ← expandElement ac (some "@reverse") value baseUrl opts false with
        | none => pure ()
        | some ev =>
          if let some rm := get? ev "@reverse" then
            for (prop, items) in entries rm do result.modify fun r => addTo r prop (arrayify items)
          let rest := (entries ev).filter (·.1 != "@reverse")
          if !rest.isEmpty then
            let mut revMap := match get? (← result.get) "@reverse" with | some m => m | none => Json.mkObj []
            for (prop, items) in rest do
              for item in arrayify items do
                if isValueObj item || isListObj item then fail "invalid reverse property value"
                revMap := addTo revMap prop [item]
            put revMap
      | "@default" =>
        if opts.frame then
          match ← expandElement ac (some "@default") value baseUrl opts false with
          | some ev => put (Json.arr (arrayify ev).toArray)
          | none => pure ()
      | "@embed" | "@explicit" | "@omitDefault" | "@requireAll" =>
        if opts.frame then put (Json.arr (arrayify value).toArray)
      | "@nest" => nests.modify fun l => if l.contains key then l else l ++ [key]
      | _ => pure ()
      continue
    -- a property
    let d := ac.find key
    let container := (d.map (·.container)).getD []
    let mut ev : Option Json := none
    if container.contains "@language" && isMap value then
      let dir : Option String := match d.bind (·.directionMapping) with | some l => l | none => ac.direction
      let mut out : Array Json := #[]
      for (lang, lv) in entries value do
        let none' := (← expandIri ac lang false true) == some "@none"
        for item in arrayify lv do
          match item with
          | .null => pure ()
          | .str _ =>
            let mut o := Json.mkObj [("@value", item)]
            if !none' then o := setKey o "@language" (Json.str lang)
            if let some x := dir then o := setKey o "@direction" (Json.str x)
            out := out.push o
          | _ => fail "invalid language map value"
      ev := some (Json.arr out)
    else if (container.contains "@index" || container.contains "@type" || container.contains "@id") && isMap value then
      let mut out : Array Json := #[]
      for (index, iv) in entries value do
        let mut mapCtx := match ac.previous with
          | some p => if container.contains "@type" then p else ac
          | none => ac
        if container.contains "@type" then
          if let some id := mapCtx.find index then
            if let some pc := id.localContext then mapCtx ← processContext mapCtx pc id.baseUrl [] false true false
        let expIndex ← expandIri mapCtx index false true
        let items := match ← expandElement mapCtx (some key) (Json.arr (arrayify iv).toArray) baseUrl opts true with
          | some (.arr a) => a.toList
          | some x => [x]
          | none => []
        for item0 in items do
          let mut item := item0
          if container.contains "@graph" && !isGraphObj item then
            item := Json.mkObj [("@graph", Json.arr #[item])]
          let idxProp := d.bind (·.indexMapping)
          if container.contains "@index" && idxProp.isSome && idxProp != some "@index" && expIndex != some "@none" then
            let ip := idxProp.get!
            let rv ← expandValue ac ip (Json.str index)
            let some pe ← expandIri ac ip false true | fail "invalid term definition"
            item := addTo item pe [rv]
            -- the index value goes first
            let others := (arrayify (get? item pe |>.getD Json.null)).filter (· != Json.null)
            item := setKey item pe (Json.arr (rv :: others.filter (· != rv)).toArray)
            if isValueObj item then fail "invalid value object"
          else if container.contains "@index" && !has item "@index" && expIndex != some "@none" then
            item := setKey item "@index" (Json.str index)
          else if container.contains "@id" && !has item "@id" && expIndex != some "@none" then
            match ← expandIri ac index true false with
            | some x => item := setKey item "@id" (Json.str x)
            | none => pure ()
          else if container.contains "@type" && expIndex != some "@none" then
            let old := match get? item "@type" with | some (.arr a) => a.toList | some x => [x] | none => []
            item := setKey item "@type" (Json.arr ((Json.str (expIndex.getD index)) :: old).toArray)
          out := out.push item
      ev := some (Json.arr out)
    else
      ev ← expandElement ac (some key) value baseUrl opts false
    let some e0 := ev | continue
    let mut e := e0
    if container.contains "@list" && !isListObj e then
      e := Json.mkObj [("@list", Json.arr (arrayify e).toArray)]
    if container.contains "@graph" && !container.contains "@id" && !container.contains "@index" then
      e := Json.arr ((arrayify e).map fun x => Json.mkObj [("@graph", Json.arr (arrayify x).toArray)]).toArray
    if d.any (·.reverse) then
      let mut revMap := match get? (← result.get) "@reverse" with | some m => m | none => Json.mkObj []
      for item in arrayify e do
        if isValueObj item || isListObj item then fail "invalid reverse property value"
        revMap := addTo revMap ep [item]
      result.modify fun r => setKey r "@reverse" revMap
    else
      result.modify fun r => addTo r ep (arrayify e)
  for nk in (← nests.get) |> sortStrings do
    let nestAc ← match ac.find nk |>.bind (·.localContext) with
      | some pc => processContext ac pc (ac.find nk |>.bind (·.baseUrl)) [] true true false
      | none => pure ac
    for nv in arrayify ((get? elem nk).getD Json.null) do
      if !isMap nv then fail "invalid @nest value"
      for (k, _) in entries nv do
        if (← expandIri ac k false true) == some "@value" then fail "invalid @nest value"
      expandEntries nestAc typeScoped activeProp nv baseUrl opts inputType result (← (IO.mkRef ([] : List String) : IO _))

end

/-- The expand API (9.1): the expanded form of a document. -/
def expandWith (input : Json) (baseIri : Option String) (expandContext : Option Json) (eo : ExpOpts) : PM Json := do
  let mut ac : Context := { base := baseIri, originalBase := baseIri }
  if let some ec := expandContext then
    let ctx := match get? ec "@context" with | some c => c | none => ec
    ac ← processContext ac ctx baseIri [] false true false
  let r ← expandElement ac none input baseIri eo false
  match r with
  | none => return Json.arr #[]
  | some (.arr a) => return Json.arr a
  | some o@(.obj _) =>
    if keysOf o == ["@graph"] then return Json.arr (arrayify (get? o "@graph" |>.getD Json.null)).toArray
    else return Json.arr #[o]
  | some x => return Json.arr #[x]

/-! ## Node map generation (API 7.1), flattening and RDF conversion -/

inductive Subj where
  | none
  | id (s : String)
  | ref (r : Json)

structure NodeMap where
  graphs : IO.Ref Json
  issued : IO.Ref (List (String × String) × Nat)

def NodeMap.new : IO NodeMap := do
  let g ← IO.mkRef (Json.mkObj [("@default", Json.mkObj [])])
  let i ← IO.mkRef (([] : List (String × String)), 0)
  pure { graphs := g, issued := i }

/-- The blank node identifier that stands for `old` (a fresh one when `old` is none). -/
def NodeMap.issue (nm : NodeMap) (old : Option String) : IO String := do
  let (m, n) ← nm.issued.get
  match old.bind (fun o => m.lookup o) with
  | some x => pure x
  | none =>
    let x := s!"_:b{n}"
    nm.issued.set ((match old with | some o => (o, x) :: m | none => m), n + 1)
    pure x

def NodeMap.update (nm : NodeMap) (g id : String) (f : Json → Json) : IO Unit :=
  nm.graphs.modify fun gs =>
    let gr := (get? gs g).getD (Json.mkObj [])
    let node := (get? gr id).getD (Json.mkObj [("@id", Json.str id)])
    setKey gs g (setKey gr id (f node))

def addVal (prop : String) (v : Json) (node : Json) : Json :=
  let arr := match get? node prop with | some (.arr a) => a.toList | _ => []
  if arr.contains v && !(isMap v && has v "@list") then node else setKey node prop (Json.arr (arr ++ [v]).toArray)

def ensureProp (prop : String) (node : Json) : Json :=
  if has node prop then node else setKey node prop (Json.arr #[])

partial def genNodeMap (nm : NodeMap) (el : Json) (graph : String) (subj : Subj) (prop : Option String)
    (list : Option (IO.Ref (Array Json))) : PM Unit := do
  match el with
  | .arr a => for x in a do genNodeMap nm x graph subj prop list
  | .obj _ =>
    let mut e := el
    if let some ts := (if has e "@value" then none else get? e "@type") then
      let mut out : Array Json := #[]
      for t in arrayify ts do
        match t with
        | .str s =>
          if isBlank s then
            let x ← nm.issue (some s)
            out := out.push (Json.str x)
          else out := out.push t
        | _ => out := out.push t
      e := setKey e "@type" (Json.arr out)
    let addToSubject (v : Json) : PM Unit := do
      match subj, prop with
      | .id s, some p => nm.update graph s (addVal p v)
      | _, _ => pure ()
    if has e "@value" then
      match list with
      | none => addToSubject e
      | some l => l.modify (·.push e)
    else if has e "@list" then
      let res ← (IO.mkRef (#[] : Array Json) : IO _)
      genNodeMap nm ((get? e "@list").getD (Json.arr #[])) graph subj prop (some res)
      let r := Json.mkObj [("@list", Json.arr (← res.get))]
      match list with
      | none => addToSubject r
      | some l => l.modify (·.push r)
    else
      if get? e "@id" == some Json.null then return
      let id ← match get? e "@id" with
        | some (.str s) => if isBlank s then nm.issue (some s) else pure s
        | _ => nm.issue none
      nm.update graph id (fun n => n)
      match subj with
      | .ref r => if let some p := prop then nm.update graph id (addVal p r)
      | .id s =>
        if let some p := prop then
          let reference := Json.mkObj [("@id", Json.str id)]
          match list with
          | none => nm.update graph s (addVal p reference)
          | some l => l.modify (·.push reference)
      | .none => pure ()
      if let some ts := get? e "@type" then
        for t in arrayify ts do nm.update graph id (addVal "@type" t)
      if let some ix := get? e "@index" then
        let gs ← nm.graphs.get
        let node := (get? ((get? gs graph).getD (Json.mkObj [])) id).getD (Json.mkObj [])
        match get? node "@index" with
        | some old => if old != ix then fail "conflicting indexes"
        | none => nm.update graph id (fun n => setKey n "@index" ix)
      if let some rv := get? e "@reverse" then
        let referenced := Json.mkObj [("@id", Json.str id)]
        for (rp, vals) in entries rv do
          for v in arrayify vals do genNodeMap nm v graph (.ref referenced) (some rp) none
      if let some g := get? e "@graph" then
        nm.graphs.modify fun gs => if has gs id then gs else setKey gs id (Json.mkObj [])
        genNodeMap nm g id .none none none
      if let some inc := get? e "@included" then genNodeMap nm inc graph .none none none
      for (p0, v) in entries e do
        if ["@id", "@type", "@index", "@reverse", "@graph", "@included"].contains p0 then continue
        let p ← if isBlank p0 then nm.issue (some p0) else pure p0
        nm.update graph id (ensureProp p)
        genNodeMap nm v graph (.id id) (some p) none
  | _ => pure ()

def nodeMapOf (expanded : Json) : PM NodeMap := do
  let nm ← (NodeMap.new : IO _)
  genNodeMap nm expanded "@default" .none none none
  return nm

/-- Flattening (API 7.2, without the optional compaction): the nodes of the default graph, sorted by id, with the named graphs inside. -/
def flattenExpanded (expanded : Json) : PM Json := do
  let nm ← nodeMapOf expanded
  let gs ← (nm.graphs.get : IO _)
  let nodesOf (g : Json) : List Json :=
    (entries g).map (·.2) |>.filter (fun n => keysOf n != ["@id"])
  let mut dflt := (get? gs "@default").getD (Json.mkObj [])
  for (gname, g) in entries gs do
    if gname == "@default" then continue
    let entry := (get? dflt gname).getD (Json.mkObj [("@id", Json.str gname)])
    dflt := setKey dflt gname (setKey entry "@graph" (Json.arr (nodesOf g).toArray))
  return Json.arr (nodesOf dflt).toArray

/-! ### RDF -/

def rdfNs : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#"
def xsdNs : String := "http://www.w3.org/2001/XMLSchema#"

def escapeLit (s : String) : String :=
  s.toList.foldl (fun acc c =>
    match c with
    | '\\' => acc ++ "\\\\"
    | '"' => acc ++ "\\\""
    | '\n' => acc ++ "\\n"
    | '\r' => acc ++ "\\r"
    | _ => acc.push c) ""

def term (s : String) : String := if isBlank s then s else "<" ++ s ++ ">"

def lit (v : String) (dt : Option String) (lang : Option String) : String :=
  "\"" ++ escapeLit v ++ "\"" ++
    (match lang with
     | some l => "@" ++ l
     | none => match dt with | some d => if d == xsdNs ++ "string" then "" else "^^<" ++ d ++ ">" | none => "")

/-- An IRI that may stand in a quad: absolute, none of the characters N-Quads forbids, and at most one `#`. -/
def validRdfIri (s : String) : Bool :=
  isAbsoluteIri s && !s.toList.any (fun c => "<>\"{}|\\^`".toList.contains c) && (s.toList.filter (· == '#')).length ≤ 1

def validRdfNode (s : String) : Bool := isBlank s || validRdfIri s

/-- Is the language tag well formed (BCP 47 shape)? -/
def wellFormedLang (l : String) : Bool :=
  match l.splitOn "-" with
  | [] => false
  | first :: rest =>
    !first.isEmpty && first.length ≤ 8 && first.toList.all Char.isAlpha &&
    rest.all fun p => !p.isEmpty && p.length ≤ 8 && p.toList.all Char.isAlphanum

/-- The shortest decimal digits and decimal exponent that read back as the same double as `n`, as (digits, e) with value 0.d1d2.. × 10^e. -/
def shortestDigits (n : JsonNumber) : String × Int :=
  let ds0 := (toString n.mantissa.natAbs).toList
  let e0 : Int := (ds0.length : Int) - (n.exponent : Int)
  let target := Float.ofScientific n.mantissa.natAbs true n.exponent
  let rec go (p : Nat) (fuel : Nat) : String × Int :=
    match fuel with
    | 0 => (ofChars ds0, e0)
    | fuel + 1 =>
      -- round the digits to p significant digits
      let (ds, e) :=
        if ds0.length ≤ p then (ds0, e0)
        else
          let keep := ds0.take p
          let nextDigit := (ds0.drop p).headD '0'
          let m := (ofChars keep).toNat!
          let m := if nextDigit ≥ '5' then m + 1 else m
          let t := toString m
          if t.length > p then (t.toList.take p, e0 + 1) else (t.toList, e0)
      let ds := (ds.reverse.dropWhile (· == '0')).reverse
      let back := Float.ofScientific (ofChars ds).toNat! (decide (((ds.length : Int) - e) > 0)) (((ds.length : Int) - e).natAbs)
      if back == target || p ≥ 17 then (ofChars ds, e) else go (p + 1) fuel
  go 1 18

/-- ECMAScript Number-to-String, as RFC 8785 asks for. -/
def jsNumber (n : JsonNumber) : String :=
  if n.mantissa == 0 then "0" else
  let neg := n.mantissa < 0
  let (ds, e) := shortestDigits n
  let k : Int := ds.length
  let body :=
    if k ≤ e && e ≤ 21 then ds ++ ofChars (List.replicate (e - k).toNat '0')
    else if 0 < e && e ≤ 21 then (ds.take e.toNat).toString ++ "." ++ (ds.drop e.toNat).toString
    else if -6 < e && e ≤ 0 then "0." ++ ofChars (List.replicate (-e).toNat '0') ++ ds
    else
      let ex := e - 1
      let sign := if ex < 0 then "-" else "+"
      (if k == 1 then ds else (ds.take 1).toString ++ "." ++ (ds.drop 1).toString) ++ "e" ++ sign ++ toString ex.natAbs
  (if neg then "-" else "") ++ body

/-- The XSD canonical double form: `5.3E0`. -/
def canonicalDouble (n : JsonNumber) : String :=
  if n.mantissa == 0 then "0.0E0" else
  let neg := n.mantissa < 0
  let (ds, e) := shortestDigits n
  let rest := ds.drop 1
  (if neg then "-" else "") ++ (ds.take 1).toString ++ "." ++ (if rest.isEmpty then "0" else rest.toString) ++ "E" ++ toString (e - 1)

def isIntegral (n : JsonNumber) : Bool :=
  n.exponent == 0 || (n.mantissa % ((10 : Int) ^ n.exponent) == 0)

def integerText (n : JsonNumber) : String :=
  if n.exponent == 0 then toString n.mantissa else toString (n.mantissa / ((10 : Int) ^ n.exponent))

structure RdfOpts where
  generalized : Bool := false
  rdfDirection : Option String := none

/-- A JSON value in the canonical form of RFC 8785 (the numbers are written as plain decimals). -/
partial def jcs (j : Json) : String :=
  match j with
  | .obj _ =>
    "{" ++ ",".intercalate ((entries j).map fun (k, v) => (Json.str k).compress ++ ":" ++ jcs v) ++ "}"
  | .arr a => "[" ++ ",".intercalate (a.toList.map jcs) ++ "]"
  | .num n =>
    jsNumber n
  | _ => j.compress

abbrev Triple := String × String × String

/-- The RDF object of a node reference, value object or list object: its term, and the triples it needs
(a list is a chain of blank nodes; a compound literal a blank node). -/
partial def objectToRdf (item : Json) (o : RdfOpts) (fresh : IO String) : IO (Option (String × List Triple)) := do
  if has item "@list" then
    let items := arrayify ((get? item "@list").getD (Json.arr #[]))
    let mut convs : List (Option (String × List Triple)) := []
    for it in items do convs := convs ++ [← objectToRdf it o fresh]
    if convs.isEmpty then return some ("<" ++ rdfNs ++ "nil>", [])
    let mut heads : List String := []
    for _ in convs do heads := heads ++ [← fresh]
    let mut triples : List Triple := []
    for (i, c) in (List.range convs.length).zip convs do
      let h := heads[i]!
      let nxt := if i + 1 < convs.length then heads[i + 1]! else "<" ++ rdfNs ++ "nil>"
      match c with
      | some (ob, extra) => triples := triples ++ extra ++ [(h, "<" ++ rdfNs ++ "first>", ob), (h, "<" ++ rdfNs ++ "rest>", nxt)]
      | none => triples := triples ++ [(h, "<" ++ rdfNs ++ "rest>", nxt)]
    return some (heads.head!, triples)
  else if has item "@value" then
    let v := (get? item "@value").getD Json.null
    let ty := (get? item "@type").bind asStr?
    let lang := (get? item "@language").bind asStr?
    let dir := (get? item "@direction").bind asStr?
    let lexical? : Option (String × Option String) :=
      if ty == some "@json" then some (jcs v, some (rdfNs ++ "JSON"))
      else match v with
        | .bool b => some ((if b then "true" else "false"), some (ty.getD (xsdNs ++ "boolean")))
        | .num n =>
          if (!isIntegral n) || ty == some (xsdNs ++ "double") || n.mantissa.natAbs ≥ 10 ^ 21 * 10 ^ n.exponent then
            some (canonicalDouble n, some (ty.getD (xsdNs ++ "double")))
          else some (integerText n, some (ty.getD (xsdNs ++ "integer")))
        | .str s => some (s, ty)
        | _ => none
    match lexical? with
    | none => return none
    | some (text, dt) =>
      if let some d := dir then
        match o.rdfDirection with
        | some "i18n-datatype" =>
          let l := (lang.getD "").toLower
          return some (lit text (some ("https://www.w3.org/ns/i18n#" ++ l ++ "_" ++ d)) none, [])
        | some "compound-literal" =>
          let b ← fresh
          let ex : List Triple := [(b, "<" ++ rdfNs ++ "value>", lit text none none)] ++
            (match lang with | some l => [(b, "<" ++ rdfNs ++ "language>", lit l.toLower none none)] | none => []) ++
            [(b, "<" ++ rdfNs ++ "direction>", lit d none none)]
          return some (b, ex)
        | _ => pure ()
      match lang with
      | some l => if wellFormedLang l then return some (lit text none (some l.toLower), []) else return none
      | none => return some (lit text dt none, [])
  else
    match (get? item "@id").bind asStr? with
    | some id => if validRdfNode id then return some (term id, []) else return none
    | none => return none

/-- The N-Quads of an expanded document. -/
def toRdfQuads (expanded : Json) (o : RdfOpts) : PM (List String) := do
  let nm ← nodeMapOf expanded
  let gs ← (nm.graphs.get : IO _)
  let counter ← (IO.mkRef 0 : IO _)
  let fresh : IO String := do
    let n ← counter.get
    counter.set (n + 1)
    pure s!"_:l{n}"
  let out ← (IO.mkRef ([] : List String) : IO _)
  for (gname, g) in entries gs do
    if gname != "@default" && !validRdfNode gname then continue
    let gTerm := if gname == "@default" then "" else " " ++ term gname
    let emit (s p ob : String) : IO Unit := out.modify (· ++ [s ++ " " ++ p ++ " " ++ ob ++ gTerm ++ " ."])
    for (sid, node) in entries g do
      if !validRdfNode sid then continue
      for (prop, vals) in entries node do
        if prop == "@id" || prop == "@index" then continue
        if prop == "@type" then
          for t in arrayify vals do
            if let some ts := asStr? t then
              if validRdfNode ts then emit (term sid) ("<" ++ rdfNs ++ "type>") (term ts)
          continue
        if isKeyword prop then continue
        if isBlank prop && !o.generalized then continue
        if !validRdfNode prop then continue
        for item in arrayify vals do
          if let some (ob, extra) ← (objectToRdf item o fresh : IO _) then
            for (es, ep, eo) in extra do emit es ep eo
            emit (term sid) (term prop) ob
  return (← (out.get : IO _)).eraseDups

/-! ## Compaction (API 6) -/

structure CompOpts where
  compactArrays : Bool := true
  relative : Bool := true
  /-- Flattening with a context always puts the nodes under `@graph`, even a single one. -/
  graph : Bool := false

def setAbs (j : Json) (k : String) (v : Json) : Json := if has j k then j else setKey j k v

def langDirKey (lang : Option String) (dir : Option String) : String :=
  match lang, dir with
  | some l, some d => l.toLower ++ "_" ++ d
  | some l, none => l.toLower
  | none, some d => "_" ++ d
  | none, none => "@null"

/-- The inverse context (6.2.? / 4.3): var → container → type/language → value → term. -/
def inverseContext (ac : Context) : Json := Id.run do
  let mut inv : Json := Json.mkObj []
  let terms := ((ac.defs.map (·.1)).toArray.qsort
    (fun a b => a.length < b.length || (a.length == b.length && a < b))).toList
  for term in terms do
    let some d := ac.find term | continue
    let some var := d.iri | continue
    let container := if d.container.isEmpty then "@none" else String.join (sortStrings d.container)
    let entry := (get? inv var).getD (Json.mkObj [])
    let cm := (get? entry container).getD (Json.mkObj
      [("@language", Json.mkObj []), ("@type", Json.mkObj []), ("@any", Json.mkObj [("@none", Json.str term)])])
    let mut tm := (get? cm "@type").getD (Json.mkObj [])
    let mut lm := (get? cm "@language").getD (Json.mkObj [])
    let mut anyM := (get? cm "@any").getD (Json.mkObj [])
    let t := Json.str term
    if d.reverse then tm := setAbs tm "@reverse" t
    else if d.typeMapping == some "@none" then
      lm := setAbs lm "@any" t
      tm := setAbs tm "@any" t
    else if let some ty := d.typeMapping then tm := setAbs tm ty t
    else if d.languageMapping.isSome || d.directionMapping.isSome then
      let key :=
        if d.languageMapping.isSome && d.directionMapping.isSome then langDirKey d.languageMapping.get! d.directionMapping.get!
        else if d.languageMapping.isSome then langDirKey d.languageMapping.get! none
        else (match d.directionMapping.get! with | some dd => "_" ++ dd | none => "@none")
      lm := setAbs lm key t
    else
      let key := if ac.language.isNone && ac.direction.isNone then "@none" else langDirKey ac.language ac.direction
      lm := setAbs lm key t
      lm := setAbs lm "@none" t
      tm := setAbs tm "@none" t
    let cm := setKey (setKey (setKey cm "@type" tm) "@language" lm) "@any" anyM
    inv := setKey inv var (setKey entry container cm)
  return inv

/-- Term selection (6.3). -/
def selectTerm (inv : Json) (var : String) (containers : List String) (tl : String) (pv : List String) : Option String := Id.run do
  let some entry := get? inv var | return none
  for c in containers do
    let some cm := get? entry c | continue
    let some tlm := get? cm tl | continue
    for p in pv do
      if let some (.str t) := get? tlm p then return some t
  return none

def compareShortestLeast (a b : String) : Bool := a.length < b.length || (a.length == b.length && a < b)

/-- A relative IRI reference for `iri` against `base` (the shortest form that resolves back). -/
def relativize (base iri : String) : String := Id.run do
  let b := parseIri base
  let r := parseIri iri
  if r.scheme != b.scheme || r.authority != b.authority then return iri
  else
    let bp := removeDotSegments b.path
    let rp := removeDotSegments r.path
    if bp == rp && r.query == b.query then
      match r.fragment with
      | some f => "#" ++ f
      | none => if r.query.isSome then "?" ++ r.query.get! else ((rp.splitOn "/").getLast?.getD "") |> fun l => if l.isEmpty then "./" else l
    else if bp == rp then "?" ++ r.query.getD "" ++ (match r.fragment with | some f => "#" ++ f | none => "")
    else
      let baseDir := (bp.splitOn "/").dropLast
      let relSegs := rp.splitOn "/"
      let mut k := 0
      while k < baseDir.length && k + 1 < relSegs.length && baseDir[k]! == relSegs[k]! do k := k + 1
      let up := baseDir.length - k
      let rest := "/".intercalate (relSegs.drop k)
      let mut out := String.join (List.replicate up "../") ++ rest
      if out.isEmpty then out := "./"
      if out.startsWith "@" then out := "./" ++ out
      if (out.toList.takeWhile (· != '/')).contains ':' then out := "./" ++ out
      out ++ (match r.query with | some q => "?" ++ q | none => "") ++ (match r.fragment with | some f => "#" ++ f | none => "")

/-- IRI compaction (6.2). -/
partial def compactIri (ac : Context) (inv : Json) (var : String) (value : Option Json) (vocab reverse : Bool) (o : CompOpts) :
    Except String String := do
  let defaultLang := if ac.language.isNone && ac.direction.isNone then "@none" else langDirKey ac.language ac.direction
  if vocab && has inv var then
    let mut containers : List String := []
    let mut tl := "@language"
    let mut tlv := "@null"
    let v0 := value.getD Json.null
    let v := if isMap v0 && has v0 "@preserve" then (arrayify ((get? v0 "@preserve").getD Json.null)).head?.getD Json.null else v0
    let hasIdx := has v "@index"
    if hasIdx && !isGraphObj v then containers := containers ++ ["@index", "@index@set"]
    if reverse then
      tl := "@type"
      tlv := "@reverse"
      containers := containers ++ ["@set"]
    else if isListObj v then
      if !hasIdx then containers := containers ++ ["@list"]
      let list := arrayify ((get? v "@list").getD (Json.arr #[]))
      if list.isEmpty then
        tl := "@any"
        tlv := "@none"
      else
        let mut commonLang : Option String := none
        let mut commonType : Option String := none
        for item in list do
          let mut itemLang := "@none"
          let mut itemType := "@none"
          if isValueObj item then
            if has item "@direction" then
              let l := ((get? item "@language").bind asStr?).getD ""
              itemLang := l.toLower ++ "_" ++ (((get? item "@direction").bind asStr?).getD "")
            else if has item "@language" then itemLang := (((get? item "@language").bind asStr?).getD "").toLower
            else if has item "@type" then itemType := ((get? item "@type").bind asStr?).getD ""
            else itemLang := "@null"
          else itemType := "@id"
          match commonLang with
          | none => commonLang := some itemLang
          | some c => if itemLang != c && isValueObj item then commonLang := some "@none"
          match commonType with
          | none => commonType := some itemType
          | some c => if itemType != c then commonType := some "@none"
          if commonLang == some "@none" && commonType == some "@none" then break
        let cl := commonLang.getD "@none"
        let ct := commonType.getD "@none"
        if ct != "@none" then
          tl := "@type"
          tlv := ct
        else tlv := cl
    else if isGraphObj v then
      if hasIdx then containers := containers ++ ["@graph@index", "@graph@index@set"]
      if has v "@id" then containers := containers ++ ["@graph@id", "@graph@id@set"]
      containers := containers ++ ["@graph", "@graph@set", "@set"]
      if !hasIdx then containers := containers ++ ["@graph@index", "@graph@index@set"]
      if !has v "@id" then containers := containers ++ ["@graph@id", "@graph@id@set"]
      containers := containers ++ ["@index", "@index@set"]
      tl := "@type"
      tlv := "@id"
    else if isValueObj v then
      if has v "@direction" && !hasIdx then
        tlv := langDirKey ((get? v "@language").bind asStr?) ((get? v "@direction").bind asStr?)
        containers := containers ++ ["@language", "@language@set"]
      else if has v "@language" && !hasIdx then
        tlv := (((get? v "@language").bind asStr?).getD "").toLower
        containers := containers ++ ["@language", "@language@set"]
      else if has v "@type" then
        tl := "@type"
        tlv := ((get? v "@type").bind asStr?).getD ""
      containers := containers ++ ["@set"]
    else
      tl := "@type"
      tlv := "@id"
      containers := containers ++ ["@id", "@id@set", "@type", "@set@type", "@set"]
    containers := containers ++ ["@none"]
    if !hasIdx then containers := containers ++ ["@index", "@index@set"]
    if isValueObj v && (keysOf v).length == 1 then containers := containers ++ ["@language", "@language@set"]
    let mut pv : List String := []
    if tlv == "@reverse" then pv := pv ++ ["@reverse"]
    if (tlv == "@id" || tlv == "@reverse") && isMap v && has v "@id" then
      let idv := ((get? v "@id").bind asStr?).getD ""
      let r ← compactIri ac inv idv none true false o
      if (ac.find r).any (fun d => d.iri == some idv) then pv := pv ++ ["@vocab", "@id", "@none"]
      else pv := pv ++ ["@id", "@vocab", "@none"]
    else
      pv := pv ++ [tlv, "@none"]
    pv := pv ++ ["@any"]
    -- a language map keeps the language in its key, so a term that fixes only the direction serves a value with both
    let dirOnly : List String :=
      if isValueObj v && has v "@direction" && has v "@language" && !hasIdx then ["_" ++ (((get? v "@direction").bind asStr?).getD "")] else []
    let mut found : Option String := none
    for c in containers do
      if found.isNone then
        let pvc := if (c == "@language" || c == "@language@set") && !dirOnly.isEmpty then pv ++ dirOnly else pv
        found := selectTerm inv var [c] tl pvc
    if let some t := found then return t
  if vocab then
    if let some vm := ac.vocab then
      if var.startsWith vm && var.length > vm.length then
        let suffix := (var.drop vm.length).toString
        if (ac.find suffix).isNone then return suffix
  let mut choice : Option String := none
  for (term, d) in ac.defs do
    let some di := d.iri | continue
    if di == var || !var.startsWith di || !d.isPrefix then continue
    let cand := term ++ ":" ++ (var.drop di.length).toString
    let usable := (ac.find cand).isNone || ((ac.find cand).any (fun cd => cd.iri == some var) && value.isNone)
    if usable && (choice.isNone || compareShortestLeast cand choice.get!) then choice := some cand
  if let some c := choice then return c
  for (term, d) in ac.defs do
    if d.isPrefix && d.iri.isSome && var.startsWith (term ++ ":") then throw "IRI confused with prefix"
  if !vocab then
    if !o.relative then return var
    match ac.base with
    | some b => return relativize b var
    | none => return var
  return var

/-- Value compaction (6.4): the scalar a value compacts to, if it does. -/
def compactValue (ac : Context) (inv : Json) (prop : Option String) (value : Json) (o : CompOpts) : Except String (Option Json) := do
  let d := prop.bind ac.find
  let container := (d.map (·.container)).getD []
  let mut result := value
  if has result "@index" && container.contains "@index" then result := delKey result "@index"
  let language : Option String := match d.bind (·.languageMapping) with | some l => l | none => ac.language
  let direction : Option String := match d.bind (·.directionMapping) with | some l => l | none => ac.direction
  let tm := d.bind (·.typeMapping)
  if has result "@id" && (keysOf result) == ["@id"] then
    match tm with
    | some "@id" =>
      let id := ((get? result "@id").bind asStr?).getD ""
      return some (Json.str (← compactIri ac inv id none false false o))
    | some "@vocab" =>
      let id := ((get? result "@id").bind asStr?).getD ""
      return some (Json.str (← compactIri ac inv id none true false o))
    | _ => return none
  if has result "@value" then
    let ty := (get? result "@type").bind asStr?
    if ty.isSome && ty == tm then return get? result "@value"
    if tm == some "@none" || ty.isSome then return none
    let v := (get? result "@value").getD Json.null
    let hasIdx := has result "@index"
    if !isStr v then
      if !hasIdx then return some v else return none
    let rl := (get? result "@language").bind asStr?
    let rd := (get? result "@direction").bind asStr?
    if hasIdx then return none
    if rl.isNone && rd.isNone then
      if language.isNone && direction.isNone then return some v else return none
    if (rl.map String.toLower) == (language.map String.toLower) && rd == direction then return some v
    return none
  return none

/-- Add a value under a key; a second value turns it into an array (the `add value` of the API). -/
def addValueTo (obj : Json) (key : String) (v : Json) (asArray : Bool) : Json :=
  let vs := match v with | .arr a => a.toList | x => [x]
  match get? obj key with
  | none =>
    if asArray || (match v with | .arr _ => true | _ => false) then setKey obj key (Json.arr vs.toArray)
    else setKey obj key v
  | some old =>
    let ol := match old with | .arr a => a.toList | x => [x]
    setKey obj key (Json.arr (ol ++ vs).toArray)

def fromE (e : Except String α) : PM α :=
  match e with
  | .ok a => pure a
  | .error m => throw m

mutual

partial def compactEl (ac0 : Context) (inv0 : Json) (activeProp : Option String) (el : Json) (o : CompOpts) : PM Json := do
  let propDef := activeProp.bind ac0.find
  let container := (propDef.map (·.container)).getD []
  match el with
  | .arr items =>
    let mut res : Array Json := #[]
    for it in items do
      let c ← compactEl ac0 inv0 activeProp it o
      if c != Json.null then res := res.push c
    if res.isEmpty || res.size > 1 || !o.compactArrays || activeProp == some "@graph" || activeProp == some "@set" ||
        container.contains "@list" || container.contains "@set" then return Json.arr res
    return res[0]!
  | .obj _ =>
    let mut ac := ac0
    let mut inv := inv0
    if let some prev := ac.previous then
      if !has el "@value" && keysOf el != ["@id"] then
        ac := prev
        inv := inverseContext prev
    if let some pd := propDef then
      if let some pc := pd.localContext then
        ac ← processContext ac pc pd.baseUrl [] true true false
        inv := inverseContext ac
    if has el "@value" || has el "@id" then
      match ← fromE (compactValue ac inv activeProp el o) with
      | some r => return r
      | none => pure ()
    if isListObj el && container.contains "@list" then
      return ← compactEl ac inv activeProp ((get? el "@list").getD (Json.arr #[])) o
    let insideReverse := activeProp == some "@reverse"
    let typeScoped := ac
    let typeScopedInv := inv
    let mut result := Json.mkObj []
    if let some ts := get? el "@type" then
      let mut cts : List String := []
      for t in arrayify ts do
        if let some tx := asStr? t then cts := cts ++ [← fromE (compactIri typeScoped typeScopedInv tx none true false o)]
      for ct in sortStrings cts do
        if let some td := typeScoped.find ct then
          if let some pc := td.localContext then
            ac ← processContext ac pc td.baseUrl [] false false false
            inv := inverseContext ac
    for (ep, ev) in entries el do
      let alias (k : String) : PM String := fromE (compactIri ac inv k none true false o)
      if ep == "@id" then
        match ev with
        | .str s =>
          let cv ← fromE (compactIri ac inv s none false false o)
          result := setKey result (← alias "@id") (Json.str cv)
        | _ => pure ()
        continue
      if ep == "@type" then
        let cts ← (arrayify ev).mapM fun t => match t with
          | .str ts => do pure (Json.str (← fromE (compactIri typeScoped typeScopedInv ts none true false o)))
          | x => do
            match get? x "@preserve" with
            | some pv =>
              let items ← (arrayify pv).mapM fun y => do
                match y with
                | .str ys => pure (Json.str (← fromE (compactIri typeScoped typeScopedInv ys none true false o)))
                | z => pure z
              pure (Json.mkObj [("@preserve", Json.arr items.toArray)])
            | none => pure x
        let al ← alias "@type"
        let asArr := (((ac.find al).map (·.container)).getD []).contains "@set" || !o.compactArrays
        result := addValueTo result al (match cts with | [x] => (if asArr then Json.arr #[x] else x) | _ => Json.arr cts.toArray) asArr
        continue
      if ep == "@reverse" then
        let cv ← compactEl ac inv (some "@reverse") ev o
        let mut rest := cv
        for (prop, val) in entries cv do
          if let some pd := ac.find prop then
            if pd.reverse then
              let asArr := pd.container.contains "@set" || !o.compactArrays
              result := addValueTo result prop (if asArr && !isArr val then Json.arr #[val] else val) asArr
              rest := delKey rest prop
        if !(entries rest).isEmpty then result := setKey result (← alias "@reverse") rest
        continue
      if ep == "@preserve" then
        let cv ← compactEl ac inv activeProp ev o
        if !(isArr cv && (arrayify cv).isEmpty) then result := addValueTo result "@preserve" cv false
        continue
      if ep == "@index" then
        if container.contains "@index" then continue
        result := setKey result (← alias "@index") ev
        continue
      if ep == "@value" || ep == "@language" || ep == "@direction" then
        result := setKey result (← alias ep) ev
        continue
      if isKeyword ep && ep != "@graph" && ep != "@list" && ep != "@included" then
        result := addValueTo result (← alias ep) ev false
        continue
      let items := arrayify ev
      let nestOf (itemProp : String) : PM (Option String) := do
        match (ac.find itemProp).bind (·.nestValue) with
        | none => pure none
        | some nt =>
          if nt != "@nest" && (← expandIri ac nt false true) != some "@nest" then fail "invalid @nest value"
          pure (some nt)
      if items.isEmpty then
        let ip ← fromE (compactIri ac inv ep (some (Json.arr #[])) true insideReverse o)
        let nt ← nestOf ip
        let target := match nt with | some n => (get? result n).getD (Json.mkObj []) | none => result
        let asArr := !o.compactArrays || (((ac.find ip).map (·.container)).getD []).contains "@set"
        let target := addValueTo target ip (Json.arr #[]) asArr
        result := match nt with | some n => setKey result n target | none => target
      for item in items do
        let ip ← fromE (compactIri ac inv ep (some item) true insideReverse o)
        let nt ← nestOf ip
        let mut target := match nt with | some n => (get? result n).getD (Json.mkObj []) | none => result
        let ipDef := ac.find ip
        let ipContainer := (ipDef.map (·.container)).getD []
        let asArr := !o.compactArrays || ipContainer.contains "@set" || ip == "@graph" || ip == "@set" || ip == "@list"
        let toCompact : Json :=
          if isListObj item then (get? item "@list").getD (Json.arr #[])
          else if isGraphObj item then (get? item "@graph").getD (Json.arr #[])
          else item
        let mut ci ← compactEl ac inv (some ip) toCompact o
        if isListObj item then
          if !ipContainer.contains "@list" then
            let cl := Json.arr (arrayify ci).toArray
            let mut w := Json.mkObj [(← alias "@list", cl)]
            if let some ix := get? item "@index" then w := setKey w (← alias "@index") ix
            target := addValueTo target ip w asArr
          else
            if has target ip then fail "compaction to list of lists"
            target := setKey target ip ci
        else if isGraphObj item then
          if ipContainer.contains "@graph" && ipContainer.contains "@id" then
            let mut m := (get? target ip).getD (Json.mkObj [])
            let key ← match (get? item "@id").bind asStr? with
              | some id => fromE (compactIri ac inv id none false false o)
              | none => pure (← alias "@none")
            m := addValueTo m key ci asArr
            target := setKey target ip m
          else if ipContainer.contains "@graph" && ipContainer.contains "@index" && !has item "@id" then
            let mut m := (get? target ip).getD (Json.mkObj [])
            let key := ((get? item "@index").bind asStr?).getD "@none"
            m := addValueTo m key ci asArr
            target := setKey target ip m
          else if ipContainer.contains "@graph" && !has item "@id" then
            if isArr ci && (arrayify ci).length > 1 then ci := Json.mkObj [(← alias "@included", ci)]
            target := addValueTo target ip ci asArr
          else
            let mut w := Json.mkObj [(← alias "@graph", ci)]
            if let some id := (get? item "@id").bind asStr? then
              w := setKey w (← alias "@id") (Json.str (← fromE (compactIri ac inv id none false false o)))
            if let some ix := get? item "@index" then w := setKey w (← alias "@index") ix
            target := addValueTo target ip w asArr
        else if (ipContainer.contains "@language" || ipContainer.contains "@index" || ipContainer.contains "@id" ||
                 ipContainer.contains "@type") && !ipContainer.contains "@graph" then
          let mut m := (get? target ip).getD (Json.mkObj [])
          let mut mapKey : Option String := none
          if ipContainer.contains "@language" && isValueObj item then
            ci := (get? item "@value").getD Json.null
            mapKey := (get? item "@language").bind asStr?
          else if ipContainer.contains "@index" then
            match ipDef.bind (·.indexMapping) with
            | some ixp =>
              let eik ← (do match ← expandIri ac ixp false true with | some x => pure x | none => pure ixp)
              let ik0 ← fromE (compactIri ac inv eik none true false o)
              let ik := if has ci ixp then ixp else ik0
              if let some vals := get? ci ik then
                let vl := arrayify vals
                match vl with
                | (.str k) :: rest =>
                  mapKey := some k
                  ci := if rest.isEmpty then delKey ci ik else setKey ci ik (if rest.length == 1 then rest.head! else Json.arr rest.toArray)
                | _ => pure ()
            | none => mapKey := (get? item "@index").bind asStr?
          else if ipContainer.contains "@id" then
            let idk ← alias "@id"
            if let some (.str k) := get? ci idk then
              mapKey := some k
              ci := delKey ci idk
          else if ipContainer.contains "@type" then
            let tk ← alias "@type"
            match (get? ci tk) with
            | some tv =>
              match arrayify tv with
              | (.str k) :: rest =>
                mapKey := some k
                ci := if rest.isEmpty then delKey ci tk else setKey ci tk (if rest.length == 1 then rest.head! else Json.arr rest.toArray)
                -- a node reference with nothing but its id compacts to the id
                if keysOf ci == [← alias "@id"] && isMap ci then
                  if let some (.str eid) := get? item "@id" then
                    match ipDef.bind (·.typeMapping) with
                    | some "@id" => ci := Json.str (← fromE (compactIri ac inv eid none false false o))
                    | some "@vocab" => ci := Json.str (← fromE (compactIri ac inv eid none true false o))
                    | _ => pure ()
              | _ => pure ()
            | none => pure ()
          let key := match mapKey with | some k => k | none => "@none"
          let key ← if mapKey.isNone then alias "@none" else pure key
          m := addValueTo m key ci asArr
          target := setKey target ip m
        else
          target := addValueTo target ip ci asArr
        result := match nt with | some n => setKey result n target | none => target
    return result
  | _ => return el

end

/-- The compact API (9.? / 6.1 with its top level): compact an expanded document against a context. -/
def compactDoc (expanded : Json) (context : Json) (baseIri : Option String) (o : CompOpts := {}) : PM Json := do
  let ctxVal := match get? context "@context" with | some c => c | none => context
  let ac0 : Context := { base := baseIri, originalBase := baseIri }
  let ac ← processContext ac0 ctxVal baseIri [] false true false
  let inv := inverseContext ac
  let mut c ← compactEl ac inv none expanded o
  let alias := fromE (compactIri ac inv "@graph" none true false o)
  match c with
  | .arr a =>
    if a.isEmpty then c := Json.mkObj []
    else c := Json.mkObj [(← alias, c)]
  | .obj _ => if o.graph && !has c "@graph" then c := Json.mkObj [(← alias, Json.arr #[c])]
  | _ => pure ()
  let ctxEmpty := match ctxVal with | .null => true | .obj _ => (entries ctxVal).isEmpty | .arr a => a.isEmpty | _ => false
  if !ctxEmpty then c := setKey c "@context" ctxVal
  return c

/-! ## RDF to JSON-LD (API 8.1) -/

inductive RTerm where
  | iri (s : String)
  | bnode (s : String)
  | lit (lex : String) (dt : String) (lang : Option String)
  deriving BEq

structure Quad where
  s : RTerm
  p : RTerm
  o : RTerm
  g : Option RTerm

def isHex (c : Char) : Bool := c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

/-- One term of an N-Quads line, starting at `cs`; returns the term and the characters after it. -/
partial def nqTerm (cs : List Char) : Except String (RTerm × List Char) := do
  let cs := cs.dropWhile (fun c => c == ' ' || c == '\t')
  match cs with
  | '<' :: rest =>
    let iri := rest.takeWhile (· != '>')
    if iri.length == rest.length then throw "invalid N-Quads: an IRI is not closed"
    pure (.iri (ofChars iri), rest.drop (iri.length + 1))
  | '_' :: ':' :: rest =>
    let lab := rest.takeWhile (fun c => !(c == ' ' || c == '\t' || c == '\n'))
    pure (.bnode ("_:" ++ ofChars lab), rest.drop lab.length)
  | '"' :: rest =>
    let mut out : List Char := []
    let mut r := rest
    let mut closed := false
    while !closed do
      match r with
      | [] => throw "invalid N-Quads: a literal is not closed"
      | '"' :: more =>
        r := more
        closed := true
      | '\\' :: e :: more =>
        let hexN (n : Nat) : Except String (Char × List Char) :=
          let ds := more.take n
          if ds.length == n && ds.all isHex then
            let v := ds.foldl (fun a c => a * 16 + (if c.isDigit then c.toNat - 48 else (c.toLower.toNat - 87))) 0
            if Nat.isValidChar v then .ok (Char.ofNat v, more.drop n) else .error "invalid N-Quads: bad escape"
          else .error "invalid N-Quads: bad escape"
        match e with
        | 't' => out := out ++ ['\t']; r := more
        | 'b' => out := out ++ ['\x08']; r := more
        | 'n' => out := out ++ ['\n']; r := more
        | 'r' => out := out ++ ['\r']; r := more
        | 'f' => out := out ++ ['\x0c']; r := more
        | '"' => out := out ++ ['"']; r := more
        | '\'' => out := out ++ ['\'']; r := more
        | '\\' => out := out ++ ['\\']; r := more
        | 'u' => let (c, m) ← hexN 4; out := out ++ [c]; r := m
        | 'U' => let (c, m) ← hexN 8; out := out ++ [c]; r := m
        | _ => throw "invalid N-Quads: bad escape"
      | c :: more =>
        out := out ++ [c]
        r := more
    let lex := ofChars out
    match r with
    | '^' :: '^' :: '<' :: more =>
      let dt := more.takeWhile (· != '>')
      pure (.lit lex (ofChars dt) none, more.drop (dt.length + 1))
    | '@' :: more =>
      let lang := more.takeWhile (fun c => c.isAlphanum || c == '-')
      pure (.lit lex (rdfNs ++ "langString") (some (ofChars lang)), more.drop lang.length)
    | _ => pure (.lit lex (xsdNs ++ "string") none, r)
  | _ => throw "invalid N-Quads: a term is expected"

def parseNQuads (text : String) : Except String (List Quad) := do
  let mut out : List Quad := []
  for line0 in text.splitOn "\n" do
    let line := (line0.trimAscii).toString
    if line.isEmpty || line.startsWith "#" then continue
    let (s, r1) ← nqTerm line.toList
    let (p, r2) ← nqTerm r1
    let (o, r3) ← nqTerm r2
    let r3 := r3.dropWhile (fun c => c == ' ' || c == '\t')
    let (g, r4) ← match r3 with
      | '.' :: _ => pure (none, r3)
      | _ => do let (g, r) ← nqTerm r3; pure (some g, r)
    let r4 := r4.dropWhile (fun c => c == ' ' || c == '\t')
    if r4.head? != some '.' then throw "invalid N-Quads: a '.' is expected"
    out := out ++ [{ s, p, o, g }]
  return out

structure FromRdfOpts where
  useNativeTypes : Bool := false
  useRdfType : Bool := false
  rdfDirection : Option String := none

def termId : RTerm → Option String
  | .iri s => some s
  | .bnode s => some s
  | .lit .. => none

/-- A decimal text of a JSON number, or none when it is not one. -/
def nativeNumber (text : String) : Option Json :=
  let t := if text.startsWith "+" then (text.drop 1).toString else text
  let t := if t.startsWith "." then "0" ++ t else if t.startsWith "-." then "-0" ++ (t.drop 1).toString else t
  let t := (t.replace ".e" ".0e").replace ".E" ".0E"
  let expDigits := (t.toList.dropWhile (fun c => c != 'e' && c != 'E')).drop 1 |>.filter Char.isDigit
  if expDigits.length > 3 then none else
  let t := if t.endsWith "." then t ++ "0" else t
  match Json.parse t with
  | .ok (j@(.num _)) => some j
  | _ => none

def rdfToObject (o : RTerm) (opts : FromRdfOpts) : PM Json := do
  match o with
  | .iri s | .bnode s => return Json.mkObj [("@id", Json.str s)]
  | .lit lex dt lang =>
    if let some l := lang then
      return Json.mkObj [("@value", Json.str lex), ("@language", Json.str l)]
    if opts.rdfDirection == some "i18n-datatype" && dt.startsWith "https://www.w3.org/ns/i18n#" then
      let rest := (dt.drop 27).toString
      let (l, d) := match splitFirst rest '_' with | some (a, b) => (a, b) | none => (rest, "")
      let mut r := Json.mkObj [("@value", Json.str lex)]
      if !l.isEmpty then r := setKey r "@language" (Json.str l)
      if !d.isEmpty then r := setKey r "@direction" (Json.str d)
      return r
    if dt == rdfNs ++ "JSON" then
      match Json.parse lex with
      | .ok j => return Json.mkObj [("@value", j), ("@type", Json.str "@json")]
      | .error _ => fail "invalid JSON literal"
    if opts.useNativeTypes then
      if dt == xsdNs ++ "string" then return Json.mkObj [("@value", Json.str lex)]
      if dt == xsdNs ++ "boolean" then
        if lex == "true" || lex == "1" then return Json.mkObj [("@value", Json.bool true)]
        if lex == "false" || lex == "0" then return Json.mkObj [("@value", Json.bool false)]
      if dt == xsdNs ++ "integer" && !lex.isEmpty && (lex.toList.all (fun c => c.isDigit || c == '-' || c == '+')) then
        if let some n := nativeNumber lex then return Json.mkObj [("@value", n)]
      if dt == xsdNs ++ "double" then
        if let some n := nativeNumber lex then return Json.mkObj [("@value", n)]
    if dt == xsdNs ++ "string" then return Json.mkObj [("@value", Json.str lex)]
    return Json.mkObj [("@value", Json.str lex), ("@type", Json.str dt)]

def rdfFirst : String := rdfNs ++ "first"
def rdfRest : String := rdfNs ++ "rest"
def rdfNil : String := rdfNs ++ "nil"
def rdfList : String := rdfNs ++ "List"

/-- RDF to JSON-LD (8.1): an expanded document from quads. -/
def fromRdf (quads : List Quad) (opts : FromRdfOpts) : PM Json := do
  let graphs ← (IO.mkRef (Json.mkObj [("@default", Json.mkObj [])]) : IO _)
  -- usages: (graph, target id, referrer id, property, value)
  let usages ← (IO.mkRef ([] : List (String × String × String × String × Json)) : IO _)
  let ensure (g id : String) : IO Unit := graphs.modify fun gs =>
    let gr := (get? gs g).getD (Json.mkObj [])
    if has gr id then gs else setKey gs g (setKey gr id (Json.mkObj [("@id", Json.str id)]))
  let upd (g id : String) (f : Json → Json) : IO Unit := graphs.modify fun gs =>
    let gr := (get? gs g).getD (Json.mkObj [])
    let n := (get? gr id).getD (Json.mkObj [("@id", Json.str id)])
    setKey gs g (setKey gr id (f n))
  for q in quads do
    let some sid := termId q.s | continue
    let some pid := termId q.p | continue
    let gname := match q.g with | some g => (termId g).getD "@default" | none => "@default"
    graphs.modify fun gs => if has gs gname then gs else setKey gs gname (Json.mkObj [])
    ensure gname sid
    if gname != "@default" then ensure "@default" gname
    let oid := termId q.o
    if let some o := oid then ensure gname o
    if pid == rdfNs ++ "type" && oid.isSome && !opts.useRdfType then
      upd gname sid (addVal "@type" (Json.str oid.get!))
      continue
    let v ← rdfToObject q.o opts
    let existing := (get? ((get? ((get? (← (graphs.get : IO _)) gname).getD (Json.mkObj [])) sid).getD (Json.mkObj [])) pid)
    let already := (arrayify (existing.getD Json.null)).contains v
    upd gname sid (addVal pid v)
    if let some o := oid then
      if !already then usages.modify (· ++ [(gname, o, sid, pid, v)])
  -- compound literals
  if opts.rdfDirection == some "compound-literal" then
    for (gname, gr) in entries (← (graphs.get : IO _)) do
      for (id, node) in entries gr do
        if has node (rdfNs ++ "direction") then
          let us := (← (usages.get : IO _)).filter (fun u => u.1 == gname && u.2.1 == id)
          if let [(_, _, ref, prop, val)] := us then
            let first (k : String) : Option Json := (get? node k).bind fun a => (arrayify a).head?
            let some (.obj _ ) := first (rdfNs ++ "value") | continue
            let valueText := ((first (rdfNs ++ "value")).bind (get? · "@value")).getD Json.null
            let mut vo := Json.mkObj [("@value", valueText)]
            if let some l := (first (rdfNs ++ "language")).bind (get? · "@value") then vo := setKey vo "@language" l
            if let some d := (first (rdfNs ++ "direction")).bind (get? · "@value") then vo := setKey vo "@direction" d
            graphs.modify fun gs =>
              let gr := (get? gs gname).getD (Json.mkObj [])
              let r := (get? gr ref).getD (Json.mkObj [])
              let arr := (arrayify ((get? r prop).getD (Json.arr #[]))).map fun x => if x == val then vo else x
              setKey gs gname (setKey (delKey gr id) ref (setKey r prop (Json.arr arr.toArray)))
  -- lists
  let converted ← (IO.mkRef ([] : List (String × Json)) : IO _)
  for (gname, _) in entries (← (graphs.get : IO _)) do
    let allUs ← (usages.get : IO _)
    let us := allUs.filter (·.1 == gname)
    let once (id : String) : Option (String × String × Json) :=
      match allUs.filter (·.2.1 == id) with
      | [(_, _, r, p, v)] => some (r, p, v)
      | _ => none
    for (_, tgt, ref0, prop0, val0) in us do
      if tgt != rdfNil then continue
      let mut node := ref0
      let mut property := prop0
      let mut head := val0
      let mut list : List Json := []
      let mut listNodes : List String := []
      let nodeOf (id : String) : IO Json := do
        pure ((get? ((get? (← graphs.get) gname).getD (Json.mkObj [])) id).getD (Json.mkObj []))
      let mut fuel := 100000
      let mut go := true
      while go && fuel > 0 do
        fuel := fuel - 1
        let nj ← nodeOf node
        let nk := (keysOf nj).length
        let okList := property == rdfRest && (once node).isSome &&
          (match get? nj rdfFirst with | some (.arr a) => a.size == 1 | _ => false) &&
          (match get? nj rdfRest with | some (.arr a) => a.size == 1 | _ => false) &&
          (nk == 3 || (nk == 4 && get? nj "@type" == some (Json.arr #[Json.str rdfList])))
        if !okList then
          go := false
        else
          let first := (arrayify ((get? nj rdfFirst).getD Json.null)).head!
          list := list ++ [first]
          listNodes := listNodes ++ [node]
          let (r, p, v) := (once node).get!
          node := r
          property := p
          head := v
          if !isBlank node then go := false
      let newHead := Json.mkObj [("@list", Json.arr list.reverse.toArray)]
      if let some (.str hid) := get? head "@id" then
        if hid != rdfNil then converted.modify (· ++ [(hid, newHead)])
      graphs.modify fun gs =>
        let gr0 := (get? gs gname).getD (Json.mkObj [])
        let gr1 := listNodes.foldl (fun g n => delKey g n) gr0
        let hostId := node
        let host := (get? gr1 hostId).getD (Json.mkObj [])
        let host2 := (entries host).foldl (fun acc (k, v) =>
          if k == "@id" || k == "@type" then acc
          else setKey acc k (match v with
            | .arr a => Json.arr (a.map fun x => if x == head then newHead else x)
            | x => x)) host
        setKey gs gname (if has gr1 hostId then setKey gr1 hostId host2 else gr1)
  -- a list that was folded into an outer list before its own turn: its reference becomes the list
  let conv ← (converted.get : IO _)
  let rec subst (fuel : Nat) (j : Json) : Json :=
    match fuel with
    | 0 => j
    | fuel + 1 =>
      match j with
      | .arr a => Json.arr (a.map (subst fuel))
      | .obj _ =>
        match entries j with
        | [("@id", .str hid)] => (match conv.lookup hid with | some l => subst fuel l | none => j)
        | es => Json.mkObj (es.map fun (k, v) => (k, subst fuel v))
      | x => x
  let gs := subst 50 (← (graphs.get : IO _))
  let dflt := (get? gs "@default").getD (Json.mkObj [])
  let mut result : Array Json := #[]
  for (id, nd) in entries dflt do
    let mut n := nd
    if let some g := get? gs id then
      if id != "@default" then
        let ns := (entries g).map (·.2) |>.filter (fun x => keysOf x != ["@id"])
        n := setKey n "@graph" (Json.arr ns.toArray)
    if keysOf n != ["@id"] then result := result.push n
  return Json.arr result

def expand (input : Json) (baseIri : Option String) (expandContext : Option Json := none) : PM Json :=
  expandWith input baseIri expandContext {}

/-! ## Framing (Framing 1.1) -/

structure FrameOpts where
  embed : String := "@once"
  explicit : Bool := false
  requireAll : Bool := false
  omitDefault : Bool := false
  omitGraph : Bool := true
  compactArrays : Bool := true

structure FState where
  graph : String
  embedded : Bool
  graphMap : Json
  uniq : IO.Ref (List (String × String))
  stack : IO.Ref (List (String × String))
  opts : FrameOpts

def isEmptyObj (j : Json) : Bool := isMap j && (entries j).isEmpty

def valuesOf (j : Json) (k : String) : List Json := (arrayify ((get? j k).getD Json.null)).filter (· != Json.null)

def frameFlag (frame : Json) (name : String) : Option Json :=
  (get? frame ("@" ++ name)).bind fun a => (arrayify a).head?

def validFrame (f : Json) : PM Json := do
  let fr ← match f with
    | .arr #[x] => pure x
    | .obj _ => pure f
    | _ => fail "invalid frame"
  if !isMap fr then fail "invalid frame"
  if let some ids := get? fr "@id" then
    let ok := (arrayify ids).all fun x => (match x with | .str t => !isBlank t | _ => false) || isEmptyObj x
    if !ok then fail "invalid frame"
  if let some ts := get? fr "@type" then
    let ok := (arrayify ts).all fun x => (match x with | .str t => !isBlank t | _ => false) || isEmptyObj x || (isMap x && has x "@default")
    if !ok then fail "invalid frame"
  return fr

def valueMatch (pattern v : Json) : Bool :=
  let v1 := get? v "@value"
  let t1 := (get? v "@type").bind asStr?
  let l1 := ((get? v "@language").bind asStr?).map String.toLower
  let lst (k : String) : List Json := match get? pattern k with | none => [] | some x => arrayify x
  let v2 := lst "@value"
  let t2 := lst "@type"
  let l2 := (lst "@language").map fun x => match x with | .str s => Json.str s.toLower | y => y
  if v2.isEmpty && t2.isEmpty && l2.isEmpty then true
  else if !(v2.any (fun x => some x == v1) || (v2.head?.any isEmptyObj)) then false
  else if !((t1.isNone && t2.isEmpty) || t2.any (fun x => asStr? x == t1) || (t1.isSome && t2.head?.any isEmptyObj)) then false
  else if !((l1.isNone && l2.isEmpty) || l2.any (fun x => asStr? x == l1) || (l1.isSome && l2.head?.any isEmptyObj)) then false
  else true

partial def filterSubject (st : FState) (subject frame : Json) (embed : String) (requireAll : Bool) : Bool := Id.run do
  let subjects := (get? st.graphMap st.graph).getD (Json.mkObj [])
  let mut wildcard := true
  let mut matchesSome := false
  for (key, fv) in entries frame do
    let mut matchThis := false
    let nodeValues := valuesOf subject key
    let frameVals := arrayify fv
    let isEmpty := frameVals.isEmpty
    if key == "@id" then
      if frameVals.head?.any isEmptyObj then matchThis := true
      else matchThis := (nodeValues.head?).any fun n => frameVals.contains n
      if !requireAll then return matchThis
    else if key == "@type" then
      wildcard := false
      if isEmpty then
        if !nodeValues.isEmpty then return false
        matchThis := true
      else if frameVals.length == 1 && isEmptyObj frameVals.head! then matchThis := !nodeValues.isEmpty
      else
        for t in frameVals do
          if isMap t && has t "@default" then matchThis := true
          else matchThis := matchThis || nodeValues.contains t
      if !requireAll then return matchThis
    else if key.startsWith "@" then continue
    else
      let thisFrame := frameVals.head?
      let hasDefault := thisFrame.any (fun f => isMap f && has f "@default")
      wildcard := false
      if nodeValues.isEmpty && hasDefault then continue
      if !nodeValues.isEmpty && isEmpty then return false
      match thisFrame with
      | none =>
        if !nodeValues.isEmpty then return false
        matchThis := true
      | some tf =>
        if isListObj tf then
          let lv := (arrayify ((get? tf "@list").getD Json.null)).head?
          match nodeValues.head? with
          | some nl =>
            if isListObj nl then
              let nlv := arrayify ((get? nl "@list").getD Json.null)
              match lv with
              | some l =>
                if isValueObj l then matchThis := nlv.any (valueMatch l)
                else if isMap l then
                  matchThis := nlv.any fun x =>
                    match (get? x "@id").bind asStr? with
                    | some i => (match get? subjects i with | some n => filterSubject st n l embed requireAll | none => false)
                    | none => false
              | none => pure ()
          | none => pure ()
        else if isValueObj tf then matchThis := nodeValues.any (valueMatch tf)
        else if isMap tf && keysOf tf == ["@id"] then
          matchThis := nodeValues.any fun nv =>
            match (get? nv "@id").bind asStr? with
            | some i => (match get? subjects i with | some n => filterSubject st n tf embed requireAll | none => false)
            | none => false
        else if isMap tf then matchThis := !nodeValues.isEmpty
        else matchThis := false
    if !matchThis && requireAll then return false
    matchesSome := matchesSome || matchThis
  return wildcard || matchesSome

def addOut (o : Json) (prop : String) (v : Json) : Json := addTo o prop [v]

mutual

partial def frameSubj (st : FState) (subjects : List String) (frameIn : Json) (top : Bool) : PM (List Json) := do
  let frame ← validFrame frameIn
  let embed ← match frameFlag frame "embed" with
    | some (.str e) => pure e
    | some (.bool true) => pure "@once"
    | some (.bool false) => pure "@never"
    | some (.obj _) => pure st.opts.embed
    | none => pure st.opts.embed
    | some _ => fail "invalid @embed value"
  if !["@always", "@never", "@once", "@first", "@last", "@link"].contains embed then fail "invalid @embed value"
  let flagB (j : Option Json) (d : Bool) : Bool := match j with | some (.bool b) => b | some (.str t) => t == "true" | _ => d
  let explicit := flagB (frameFlag frame "explicit") st.opts.explicit
  let requireAll := flagB (frameFlag frame "requireAll") st.opts.requireAll
  let sg := (get? st.graphMap st.graph).getD (Json.mkObj [])
  let mut matched : List String := []
  for id in subjects do
    if let some n := get? sg id then
      if filterSubject st n frame embed requireAll then matched := matched ++ [id]
  let mut results : List Json := []
  for id in sortStrings matched do
    let subject := (get? sg id).getD (Json.mkObj [])
    if top then st.uniq.set []
    let mut output := Json.mkObj [("@id", Json.str id)]
    if !st.embedded && !top && (← st.uniq.get).contains (st.graph, id) then continue
    if st.embedded then
      let stack ← st.stack.get
      if embed == "@never" || stack.contains (st.graph, id) then
        results := results ++ [output]
        continue
      if (embed == "@once" || embed == "@first") && (← st.uniq.get).contains (st.graph, id) then
        results := results ++ [output]
        continue
    st.uniq.modify (fun l => (st.graph, id) :: l)
    st.stack.modify (fun l => (st.graph, id) :: l)
    if has st.graphMap id then
      let (recurse, subframe) :=
        if !has frame "@graph" then (st.graph != "@merged", Json.mkObj [])
        else
          let sf := match (arrayify ((get? frame "@graph").getD Json.null)).head? with | some x => if isMap x then x else Json.mkObj [] | none => Json.mkObj []
          (!(id == "@merged" || id == "@default"), sf)
      if recurse then
        let gk := keysOf ((get? st.graphMap id).getD (Json.mkObj []))
        let outs ← frameSubj { st with graph := id, embedded := false } gk (Json.arr #[subframe]) false
        if !outs.isEmpty then output := setKey output "@graph" (Json.arr outs.toArray)
    if let some inc := get? frame "@included" then
      let outs ← frameSubj { st with embedded := false } subjects inc false
      if !outs.isEmpty then output := setKey output "@included" (Json.arr outs.toArray)
    for (prop, objs) in entries subject do
      if isKeyword prop then
        if prop != "@id" then output := setKey output prop objs
        continue
      if explicit && !has frame prop then continue
      let implicit := Json.arr #[Json.mkObj [("@embed", Json.arr #[Json.str embed]), ("@explicit", Json.arr #[Json.bool explicit]),
                                           ("@requireAll", Json.arr #[Json.bool requireAll])]]
      let subframe := if has frame prop then (get? frame prop).getD implicit else implicit
      for o in arrayify objs do
        if isListObj o then
          let lf := match (arrayify subframe).head? with
            | some f => (match get? f "@list" with | some l => l | none => implicit)
            | none => implicit
          let mut list := Json.mkObj [("@list", Json.arr #[])]
          output := addOut output prop (Json.mkObj [])   -- placeholder, replaced below
          let mut items : Array Json := #[]
          for oo in arrayify ((get? o "@list").getD Json.null) do
            if isMap oo && keysOf oo == ["@id"] then
              let outs ← frameSubj { st with embedded := true } [((get? oo "@id").bind asStr?).getD ""] lf false
              items := items ++ outs.toArray
            else items := items.push oo
          list := Json.mkObj [("@list", Json.arr items)]
          -- replace the placeholder
          let cur := arrayify ((get? output prop).getD Json.null)
          output := setKey output prop (Json.arr ((cur.dropLast) ++ [list]).toArray)
        else if isMap o && keysOf o == ["@id"] then
          let outs ← frameSubj { st with embedded := true } [((get? o "@id").bind asStr?).getD ""] subframe false
          for out in outs do output := addOut output prop out
        else
          let sf := (arrayify subframe).head?.getD (Json.mkObj [])
          if valueMatch sf o then output := addOut output prop o
    -- defaults
    for (prop, fv) in entries frame do
      if prop == "@type" then
        let f0 := (arrayify fv).head?
        if !(f0.any fun x => isMap x && has x "@default") then continue
      else if prop.startsWith "@" then continue
      let next := (arrayify fv).head?.getD (Json.mkObj [])
      let omitD := match frameFlag next "omitDefault" with | some (.bool b) => b | some (.str t) => t == "true" | _ => st.opts.omitDefault
      if !omitD && !has output prop then
        let preserve : Json := match get? next "@default" with
          | some d => Json.arr (arrayify d).toArray
          | none => Json.arr #[Json.str "@null"]
        output := setKey output prop (Json.arr #[Json.mkObj [("@preserve", preserve)]])
    -- reverse
    if let some rf := get? frame "@reverse" then
      for (rp, sub) in entries rf do
        for sid in keysOf sg do
          let nodeVals := valuesOf ((get? sg sid).getD (Json.mkObj [])) rp
          if nodeVals.any (fun v => (get? v "@id").bind asStr? == some id) then
            let outs ← frameSubj { st with embedded := true } [sid] sub false
            let rev := (get? output "@reverse").getD (Json.mkObj [])
            let rev := if has rev rp then rev else setKey rev rp (Json.arr #[])
            let rev := setKey rev rp (Json.arr ((arrayify ((get? rev rp).getD Json.null)) ++ outs).toArray)
            output := setKey output "@reverse" rev
    st.stack.modify (·.drop 1)
    results := results ++ [output]
  return results

end

/-- `@preserve` entries are replaced by their first value. -/
partial def cleanPreserve (j : Json) : Json :=
  match j with
  | .arr a => Json.arr (a.map cleanPreserve)
  | .obj _ =>
    match get? j "@preserve" with
    | some p => cleanPreserve (match p with | .arr a => a.toList.head?.getD Json.null | x => x)
    | none => Json.mkObj ((entries j).map fun (k, v) => (k, cleanPreserve v))
  | x => x

/-- `@null` becomes null; an array holding only null is emptied. -/
partial def cleanNull (j : Json) : Json :=
  match j with
  | .str "@null" => Json.null
  | .arr a =>
    let items := a.map cleanNull
    if items.size > 0 && items.all (· == Json.null) then Json.arr #[] else Json.arr items
  | .obj _ => Json.mkObj ((entries j).map fun (k, v) => (k, cleanNull v))
  | x => x

/-- How often each blank node identifier is used by a node object or a `@type` in the result. -/
partial def bnodeUses (j : Json) (acc : List (String × Nat)) : List (String × Nat) :=
  let bump (acc : List (String × Nat)) (id : String) : List (String × Nat) :=
    if (acc.lookup id).isSome then acc.map fun (k, n) => if k == id then (k, n + 1) else (k, n) else acc ++ [(id, 1)]
  match j with
  | .arr a => a.foldl (fun acc x => bnodeUses x acc) acc
  | .obj _ =>
    let acc := match get? j "@id" with | some (.str s) => if isBlank s then bump acc s else acc | _ => acc
    let acc := (valuesOf j "@type").foldl (fun acc t => match t with | .str s => if isBlank s then bump acc s else acc | _ => acc) acc
    (entries j).foldl (fun acc (k, v) => if k == "@id" then acc else bnodeUses v acc) acc
  | _ => acc

partial def pruneBnodes (counts : List (String × Nat)) (j : Json) : Json :=
  match j with
  | .arr a => Json.arr (a.map (pruneBnodes counts))
  | .obj _ =>
    let es := (entries j).filterMap fun (k, v) =>
      if k == "@id" then
        match v with
        | .str s => if isBlank s && counts.lookup s == some 1 then none else some (k, v)
        | _ => some (k, v)
      else some (k, pruneBnodes counts v)
    Json.mkObj es
  | x => x

/-- The frame API: frame `input` by `frame`. -/
def frameDoc (input frame : Json) (baseIri : Option String) (fo : FrameOpts := {}) : PM Json := do
  let expandedInput ← expand input baseIri
  let expandedFrame ← expandWith frame baseIri none { frame := true }
  let ctx := (get? frame "@context").getD (Json.mkObj [])
  let fctx ← processContext ({ base := baseIri, originalBase := baseIri } : Context) ((get? frame "@context").getD Json.null) baseIri [] false true false
  let mut hasGraph := false
  for (k, _) in entries frame do
    if k != "@context" && (← expandIri fctx k false true) == some "@graph" then hasGraph := true
  let nm ← nodeMapOf expandedInput
  let gm ← (nm.graphs.get : IO _)
  -- merge the named graphs and the default graph
  let mut graphMap := gm
  let mut graphName := "@default"
  if !hasGraph then
    let mut merged := Json.mkObj []
    for (_, g) in entries gm do
      for (id, node) in entries g do
        let mut m := (get? merged id).getD (Json.mkObj [("@id", Json.str id)])
        for (p, vs) in entries node do
          if p == "@id" then continue
          for v in arrayify vs do m := addVal p v m
        merged := setKey merged id m
    graphMap := setKey graphMap "@merged" merged
    graphName := "@merged"
  let uniq ← (IO.mkRef ([] : List (String × String)) : IO _)
  let stack ← (IO.mkRef ([] : List (String × String)) : IO _)
  let st : FState := { graph := graphName, embedded := false, graphMap, uniq, stack, opts := fo }
  let subjects := keysOf ((get? graphMap graphName).getD (Json.mkObj []))
  let fr := match expandedFrame with
    | .arr a => (if a.isEmpty then Json.arr #[Json.mkObj []] else expandedFrame)
    | x => Json.arr #[x]
  let outs ← frameSubj st subjects fr true
  let results := Json.arr outs.toArray
  let results := pruneBnodes (bnodeUses results []) results
  let ac ← processContext ({ base := baseIri, originalBase := baseIri } : Context) ctx baseIri [] false true false
  let inv := inverseContext ac
  let co : CompOpts := { compactArrays := fo.compactArrays }
  let mut c ← compactEl ac inv none results co
  let graphAlias ← fromE (compactIri ac inv "@graph" none true false co)
  match c with
  | .arr a => c := if a.isEmpty then Json.mkObj [] else Json.mkObj [(graphAlias, c)]
  | _ => pure ()
  let ctxEmpty := match ctx with | .null => true | .obj _ => (entries ctx).isEmpty | .arr a => a.isEmpty | _ => false
  if !ctxEmpty then c := setKey c "@context" ctx
  c := cleanNull (cleanPreserve c)
  if !fo.omitGraph then
    match get? c graphAlias with
    | some (.arr _) => pure ()
    | _ =>
      let rest := (entries c).filter (·.1 != "@context")
      let body := Json.mkObj rest
      c := Json.mkObj ([(graphAlias, Json.arr (if rest.isEmpty then #[] else #[body]))] ++ ((entries c).filter (·.1 == "@context")))
  return c

end JsonLd
