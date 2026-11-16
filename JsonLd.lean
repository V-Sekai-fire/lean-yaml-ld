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
      match ← exp term false true with
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
      let some inner := get? doc "@context" | fail "invalid remote context"
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
      if keysOf r == ["@id"] && !opts.frame then return none
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
    let some ep ← expandIri ac key false true | continue
    if !ep.contains ':' && !isKeyword ep then continue
    if isKeyword ep then
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
        | .obj _ => if opts.frame then put value else fail "invalid @id value"
        | .arr a => if opts.frame && a.all isStr then put value else fail "invalid @id value"
        | _ => fail "invalid @id value"
      | "@type" =>
        let vs : List String ← match value with
          | .str s => pure [s]
          | .arr a => a.toList.mapM fun x => match x with | .str s => pure s | _ => fail "invalid type value"
          | _ => fail "invalid type value"
        let mut out : List Json := []
        for t in vs do
          match ← expandIri typeScoped t true true with
          | some x => out := out ++ [Json.str x]
          | none => pure ()
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
        | .str _ => put value
        | _ => fail "invalid language-tagged string"
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
def expand (input : Json) (baseIri : Option String) (expandContext : Option Json := none) : PM Json := do
  let mut ac : Context := { base := baseIri, originalBase := baseIri }
  if let some ec := expandContext then
    let ctx := match get? ec "@context" with | some c => c | none => ec
    ac ← processContext ac ctx baseIri [] false true false
  let r ← expandElement ac none input baseIri {} false
  match r with
  | none => return Json.arr #[]
  | some (.arr a) => return Json.arr a
  | some o@(.obj _) =>
    if keysOf o == ["@graph"] then return Json.arr (arrayify (get? o "@graph" |>.getD Json.null)).toArray
    else return Json.arr #[o]
  | some x => return Json.arr #[x]

end JsonLd
