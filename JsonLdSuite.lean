import JsonLd
import JsonLd.Remote
import YamlLd
import HtmlScripts

/-! `jsonld_suite <tests-dir> <manifest.jsonld> [id-filter]`: run a JSON-LD test manifest (json-ld/json-ld-api or yaml-ld) against the processor.
Only the tests the processor implements are run; the others are listed as skipped, never as passed. -/

open Lean JsonLd

def testsPrefix : String := "https://w3c.github.io/json-ld-api/tests/"
def yamlPrefix : String := "https://w3c.github.io/yaml-ld/tests/"
def framingPrefix : String := "https://w3c.github.io/json-ld-framing/tests/"

/-- Order-free equality for JSON-LD: arrays are sets, except the value of `@list`. -/
partial def canon (inList : Bool) (j : Json) : Json :=
  match j with
  | .arr a =>
    let items := a.toList.map (canon false)
    if inList then Json.arr items.toArray
    else Json.arr ((items.toArray.qsort (fun x y => x.compress < y.compress)))
  | .obj _ => Json.mkObj ((entries j).map fun (k, v) => (k, canon (k == "@list") v))
  | _ => j

/-- The error code of a failed read: the reader's own code where the specification has one. -/
def readCode (e : String) : String :=
  if e.startsWith "mapping-key-error" then "mapping-key-error"
  else if e.startsWith "invalid-encoding" then "invalid encoding"
  else "loading document failed"

/-- The documents in the script elements of an HTML file: the one the fragment names, the first, or all. -/
def readHtmlText (t : String) (frag : Option String) (all : Bool) : IO (Except String (Array Json)) := do
  do
    let found := HtmlScripts.extract t
    -- a YAML script may hold a stream of documents; with all scripts wanted, each is one
    let parseMany (sc : HtmlScripts.Script) : Except String (Array Json) :=
      let ty := (sc.type.trimAscii.toString.splitOn ";").head!.trimAscii.toString.toLower
      let r := if ty == "application/ld+yaml" then (if all then YamlLd.parseAll sc.text else (fun d => #[d]) <$> YamlLd.parse sc.text)
               else (fun d => #[d]) <$> Json.parse sc.text
      match r with | .ok j => .ok j | .error _ => .error "invalid script element"
    let parse (sc : HtmlScripts.Script) : Except String Json := (parseMany sc).map fun a => a[0]?.getD Json.null
    match frag with
    | some f =>
      match found.scripts.find? (·.id == some f) with
      | some sc => pure (if HtmlScripts.isLd sc then parseMany sc else .error "loading document failed")
      | none => pure (.error "loading document failed")
    | none =>
      let lds := found.scripts.filter HtmlScripts.isLd
      if lds.isEmpty then pure (if all then .ok #[] else .error "loading document failed")
      else if all then pure ((lds.mapM parseMany).map (·.flatten))
      else pure ((parse (lds[0]?.getD ⟨none, "", ""⟩)).map (fun j => #[j]))

def readHtml (file : String) (frag : Option String) (all : Bool) : IO (Except String (Array Json)) := do
  match ← YamlLd.readText file with
  | .error e => pure (.error (readCode e))
  | .ok t => readHtmlText t frag all

/-- The `href` of the first `<base>` element of an HTML file. -/
def htmlBase (file : String) : IO (Option String) := do
  match ← YamlLd.readText file with
  | .ok t => pure (HtmlScripts.extract t).base
  | .error _ => pure none

def readDocs (path : String) (all : Bool) : IO (Except String (Array Json)) := do
  if (path.splitOn "#").head!.endsWith ".html" then
    let parts := path.splitOn "#"
    return ← readHtml parts.head! (if parts.length > 1 then some (String.intercalate "#" parts.tail!) else none) all
  match ← YamlLd.readText path with
  | .error e => pure (.error (readCode e))
  | .ok t =>
    if path.endsWith ".yamlld" || path.endsWith ".yaml" then
      match (if all then YamlLd.parseAll t else (fun d => #[d]) <$> YamlLd.parse t) with
      | .ok ds => pure (.ok ds)
      | .error e => pure (.error (readCode e))
    else pure (match Json.parse t with | .ok j => .ok #[j] | .error _ => .error "loading document failed")

def readDoc (path : String) : IO (Except String Json) := do
  match ← readDocs path false with
  | .ok ds => pure (.ok (ds[0]?.getD Json.null))
  | .error e => pure (.error e)

/-- The pieces of a line around its blank node labels: `_:label` replaced by `f label`. -/
def relabel (line : String) (f : String → String) : String :=
  match line.splitOn "_:" with
  | [] => line
  | first :: rest =>
    first ++ String.join (rest.map fun piece =>
      let cs := piece.toList
      let lab := cs.takeWhile (fun c => c.isAlphanum || c == '_' || c == '-')
      f ("_:" ++ ofChars lab) ++ ofChars (cs.drop lab.length))

def labelsOf (line : String) : List String :=
  match line.splitOn "_:" with
  | [] => []
  | _ :: rest => rest.map fun piece => "_:" ++ ofChars (piece.toList.takeWhile (fun c => c.isAlphanum || c == '_' || c == '-'))

/-- Quads in a form that does not depend on the names of blank nodes: each is named by what is said about it (colour refinement). -/
def canonQuads (lines : List String) : List String := Id.run do
  let bnodes := (lines.flatMap labelsOf).eraseDups
  let mut color : List (String × String) := bnodes.map (·, "")
  for _ in [0:6] do
    let mut next : List (String × String) := []
    for b in bnodes do
      let sig := (lines.filter (fun l => (labelsOf l).contains b)).map fun l =>
        relabel l (fun x => if x == b then "_:SELF" else "_:" ++ ((color.lookup x).getD ""))
      let sorted := (sig.toArray.qsort (· < ·)).toList
      next := next ++ [(b, toString (hash ("|".intercalate sorted)))]
    color := next
  let out := lines.map fun l => relabel l (fun x => "_:" ++ ((color.lookup x).getD ""))
  return ((out.toArray.qsort (· < ·)).toList).eraseDups

def main (args : List String) : IO UInt32 := do
  let (dir, manifest, filter) ← match args with
    | [d, m] => pure (d, m, "")
    | [d, m, f] => pure (d, m, f)
    | _ => IO.eprintln "usage: jsonld_suite <tests-dir> <manifest.jsonld> [id-filter]"; return 2
  -- A document outside the test suite needs the network; a test that fails after asking for one is skipped, not failed.
  let curId ← IO.mkRef ""
  let unreached ← IO.mkRef (#[] : Array String)
  let loader : String → IO (Except String Json) := fun url => do
    let rel? := if url.startsWith testsPrefix then some (url.drop testsPrefix.length).toString
      else if url.startsWith yamlPrefix then some (url.drop yamlPrefix.length).toString
      else if url.startsWith framingPrefix then some (url.drop framingPrefix.length).toString else none
    match rel? with
    | some rel => readDoc (dir ++ "/" ++ rel)
    | none => do
      -- Lean's standard library has no TLS client, so a document outside the suite is fetched with curl.
      let out ← IO.Process.output { cmd := "curl", args := #["-sSL", "--max-time", "20", "-H", "Accept: application/ld+json, application/json", url] } |>.toBaseIO
      match out with
      | .ok o =>
        if o.exitCode == 0 then
          match Json.parse o.stdout with
          | .ok j => pure (.ok j)
          | .error e => pure (.error s!"{url} is not JSON: {e}")
        else do unreached.modify (·.push (← curId.get)); pure (.error s!"cannot fetch {url}")
      | .error _ => do unreached.modify (·.push (← curId.get)); pure (.error s!"cannot fetch {url}")
  let some mtext ← (do match ← YamlLd.readText manifest with | .ok t => pure (some t) | .error _ => pure none) | IO.eprintln "no manifest"; return 2
  let .ok m := Json.parse mtext | IO.eprintln "bad manifest"; return 2
  let mut pass := 0
  let mut fails : List String := []
  let mut skips : List String := []
  for t in arrayify ((get? m "sequence").getD Json.null) do
    let id := ((get? t "@id").bind asStr?).getD ""
    curId.set id
    if !filter.isEmpty && !(id.endsWith filter) then continue
    let kinds := (arrayify ((get? t "@type").getD Json.null)).filterMap asStr?
    let toRdf := kinds.contains "jld:ToRDFTest"
    let flat := kinds.contains "jld:FlattenTest"
    let comp := kinds.contains "jld:CompactTest"
    if kinds.contains "jld:FrameTest" then
      let opts := (get? t "option").getD (Json.mkObj [])
      if get? opts "specVersion" == some (Json.str "json-ld-1.0") || get? opts "processingMode" == some (Json.str "json-ld-1.0") then
        skips := skips ++ [id ++ " (option)"]; continue
      let some input := (get? t "input").bind asStr? | skips := skips ++ [id]; continue
      let some framePath := (get? t "frame").bind asStr? | skips := skips ++ [id]; continue
      let docUrl := framingPrefix ++ input
      let fo : FrameOpts := { omitGraph := get? opts "omitGraph" != some (Json.bool false) }
      let r : Except String Json ← do
        match ← readDoc (dir ++ "/" ++ input), ← readDoc (dir ++ "/" ++ framePath) with
        | .ok doc, .ok fr => (((frameDoc doc fr (some docUrl) fo).run { loader, bareContext := fun u => u.endsWith ".yamlld" || u.endsWith ".yaml" }).run : IO _)
        | _, _ => pure (.error "loading document failed")
      if kinds.contains "jld:NegativeEvaluationTest" then
        let want := ((get? t "expectErrorCode").bind asStr?).getD ""
        match r with
        | .error e => if e == want then pass := pass + 1 else fails := fails ++ [s!"{id}: want '{want}', got '{e}'"]
        | .ok _ => fails := fails ++ [s!"{id}: want error '{want}', got a result"]
      else
        let some ep := (get? t "expect").bind asStr? | skips := skips ++ [id]; continue
        match r, ← readDoc (dir ++ "/" ++ ep) with
        | .ok got, .ok want =>
          if canon false got == canon false want then pass := pass + 1
          else
            let detail := if filter.isEmpty then "" else "\n got  " ++ got.compress ++ "\n want " ++ want.compress
            fails := fails ++ [id ++ ": differs" ++ detail]
        | .error e, _ => fails := fails ++ [s!"{id}: error '{e}'"]
        | _, .error e => fails := fails ++ [s!"{id}: cannot read expected output {e}"]
      continue
    if kinds.contains "jld:FromRDFTest" then
      let opts := (get? t "option").getD (Json.mkObj [])
      if get? opts "specVersion" == some (Json.str "json-ld-1.0") || get? opts "processingMode" == some (Json.str "json-ld-1.0") then
        skips := skips ++ [id ++ " (option)"]; continue
      let some input := (get? t "input").bind asStr? | skips := skips ++ [id]; continue
      let fo : FromRdfOpts := { useNativeTypes := get? opts "useNativeTypes" == some (Json.bool true),
                                useRdfType := get? opts "useRdfType" == some (Json.bool true),
                                rdfDirection := (get? opts "rdfDirection").bind asStr? }
      let r : Except String Json ← match ← YamlLd.readText (dir ++ "/" ++ input) with
        | .error e => pure (.error e)
        | .ok text =>
          match parseNQuads text with
          | .error _ => pure (.error "loading document failed")
          | .ok qs => (((fromRdf qs fo).run { loader, bareContext := fun u => u.endsWith ".yamlld" || u.endsWith ".yaml" }).run : IO _)
      if kinds.contains "jld:NegativeEvaluationTest" then
        let want := ((get? t "expectErrorCode").bind asStr?).getD ""
        match r with
        | .error e => if e == want then pass := pass + 1 else fails := fails ++ [s!"{id}: want '{want}', got '{e}'"]
        | .ok _ => fails := fails ++ [s!"{id}: want error '{want}', got a result"]
      else
        let some ep := (get? t "expect").bind asStr? | skips := skips ++ [id]; continue
        match r, ← readDoc (dir ++ "/" ++ ep) with
        | .ok got, .ok want =>
          if canon false got == canon false want then pass := pass + 1
          else
            let detail := if filter.isEmpty then "" else "\n got  " ++ got.compress ++ "\n want " ++ want.compress
            fails := fails ++ [id ++ ": differs" ++ detail]
        | .error e, _ => fails := fails ++ [s!"{id}: error '{e}'"]
        | _, .error e => fails := fails ++ [s!"{id}: cannot read expected output {e}"]
      continue
    if !kinds.contains "jld:ExpandTest" && !toRdf && !flat && !comp then skips := skips ++ [id ++ " (not an expand test)"]; continue
    let opts := (get? t "option").getD (Json.mkObj [])
    let isRemote := manifest.contains "remote-doc"
    if (!isRemote && ((has opts "contentType" && !((get? t "input").bind asStr?).any (·.contains ".html")) || has opts "redirectTo" || has opts "httpLink")) || get? opts "processingMode" == some (Json.str "json-ld-1.0")
        || get? opts "specVersion" == some (Json.str "json-ld-1.0") || has opts "extendedYAML" then
      skips := skips ++ [id ++ " (option)"]; continue
    let some input := (get? t "input").bind asStr? | skips := skips ++ [id]; continue
    let isNeg := kinds.contains "jld:NegativeEvaluationTest"
    let docUrl := (if input.startsWith "cases/" && manifest.contains "yaml" then yamlPrefix else testsPrefix) ++ input
    -- upstream: te006 expects `loading document failed` for an HTML file with no script, and tr006 expects empty output for the same file
    if id == "#tr006" then skips := skips ++ [id ++ " (contradicts #te006)"]; continue
    let optBase := ((get? opts "base").bind asStr?).getD docUrl
    let mut base ← if (input.splitOn "#").head!.endsWith ".html" then
        match ← htmlBase (dir ++ "/" ++ (input.splitOn "#").head!) with
        | some h => pure (JsonLd.resolveIri optBase h)
        | none => pure optBase
      else pure optBase
    let mut ec ← match (get? opts "expandContext").bind asStr? with
      | some p => do match ← readDoc (dir ++ "/" ++ p) with | .ok j => pure (some j) | .error _ => pure none
      | none => pure none
    let all := get? opts "extractAllScripts" == some (Json.bool true)
    let docs ← if !isRemote then readDocs (dir ++ "/" ++ input) all else do
      -- a mock server for the test: the manifest's options say what it answers for the test's own URL
      let strs (j : Option Json) : Array String := match j with
        | some (.str x) => #[x] | some (.arr a) => a.filterMap asStr? | _ => #[]
      let fetch : String → IO (Except String JsonLd.Remote.Response) := fun u => do
        if u == docUrl && has opts "redirectTo" then
          let st := match get? opts "httpStatus" with | some (.num n) => n.mantissa.toNat | _ => 302
          return .ok { status := st, location := some (testsPrefix ++ ((get? opts "redirectTo").bind asStr?).getD "") }
        let path := dir ++ "/" ++ (u.drop testsPrefix.length).toString
        if !(← System.FilePath.pathExists path) then return .ok { status := 404 }
        let ct := if u == docUrl && has opts "contentType" then ((get? opts "contentType").bind asStr?).getD ""
          else if path.endsWith ".jsonld" then "application/ld+json" else if path.endsWith ".json" then "application/json"
          else if path.endsWith ".html" then "text/html" else "application/octet-stream"
        let links := if u == docUrl then strs (get? opts "httpLink") else #[]
        return .ok { status := 200, contentType := ct, links, body := (← IO.FS.readFile path) }
      match ← JsonLd.Remote.load fetch docUrl with
      | .error e => pure (.error e)
      | .ok rd =>
        if !has opts "base" then base := rd.documentUrl
        ec := rd.contextUrl.map Json.str
        if JsonLd.Remote.isHtml rd.contentType then readHtmlText rd.body none all
        else pure (match Json.parse rd.body with | .ok j => .ok #[j] | .error _ => .error "loading document failed")
    let mut r : Except String Json := .ok (Json.arr #[])
    match docs with
    | .error e => r := .error e
    | .ok js =>
      let items := if all then #[Json.arr js] else js
      let mut acc : Array Json := #[]
      for j in items do
        match ← (((expandWith j (some base) ec { keepIdOnly := input.endsWith ".yamlld" || input.endsWith ".yaml" }).run { loader, bareContext := fun u => u.endsWith ".yamlld" || u.endsWith ".yaml" }).run : IO _) with
        | .ok (.arr a) => acc := acc ++ a
        | .ok x => acc := acc.push x
        | .error e => r := .error e; break
      if r.toOption.isSome then r := .ok (Json.arr acc)
    let copts : CompOpts := { compactArrays := get? opts "compactArrays" != some (Json.bool false),
                              relative := get? opts "compactToRelative" != some (Json.bool false), graph := flat }
    if flat || comp then
      if let .ok ex := r then
        let ex2 ← if flat then (((flattenExpanded ex).run { loader, bareContext := fun u => u.endsWith ".yamlld" || u.endsWith ".yaml" }).run : IO _) else pure (.ok ex)
        match ex2 with
        | .error e => r := .error e
        | .ok fx =>
          if has t "context" then
            match (get? t "context").bind asStr? with
            | some cp =>
              match ← readDoc (dir ++ "/" ++ cp) with
              | .ok cj => r ← (((compactDoc fx cj (some base) copts).run { loader, bareContext := fun u => u.endsWith ".yamlld" || u.endsWith ".yaml" }).run : IO _)
              | .error e => r := .error e
            | none => r := .ok fx
          else r := .ok fx
    if isNeg then
      let want := ((get? t "expectErrorCode").bind asStr?).getD ""
      let mut r2 : Except String Json := r
      if toRdf then
        if let .ok ex := r then
          let q ← (((toRdfQuads ex {}).run { loader, bareContext := fun u => u.endsWith ".yamlld" || u.endsWith ".yaml" }).run : IO _)
          if let .error e := q then r2 := .error e
      match r2 with
      | .error e => if e == want then pass := pass + 1 else fails := fails ++ [s!"{id}: want '{want}', got '{e}'"]
      | .ok _ => fails := fails ++ [s!"{id}: want error '{want}', got a result"]
    else
      let some ep := (get? t "expect").bind asStr? | skips := skips ++ [id]; continue
      if toRdf then
        let ro : RdfOpts := { generalized := get? opts "produceGeneralizedRdf" == some (Json.bool true),
                              rdfDirection := (get? opts "rdfDirection").bind asStr? }
        let q : Except String (List String) ← match r with
          | .error e => pure (.error e)
          | .ok ex => (((toRdfQuads ex ro).run { loader, bareContext := fun u => u.endsWith ".yamlld" || u.endsWith ".yaml" }).run : IO _)
        match q, ← YamlLd.readText (dir ++ "/" ++ ep) with
        | .ok lines, .ok want =>
          let wl := (want.splitOn "\n").map String.trimAscii |>.map (·.toString) |>.filter (· != "")
          if canonQuads lines == canonQuads wl then pass := pass + 1
          else
            let detail := if filter.isEmpty then "" else "\n got\n" ++ "\n".intercalate lines ++ "\n want\n" ++ "\n".intercalate wl
            fails := fails ++ [id ++ ": differs" ++ detail]
        | .error e, _ => fails := fails ++ [s!"{id}: error '{e}'"]
        | _, .error e => fails := fails ++ [s!"{id}: cannot read expected output {e}"]
        continue
      match r, ← readDoc (dir ++ "/" ++ ep) with
      | .ok got, .ok want =>
        if canon false got == canon false want then pass := pass + 1
        else
          let detail := if filter.isEmpty then "" else "\n got  " ++ got.compress ++ "\n want " ++ want.compress
          fails := fails ++ [id ++ ": differs" ++ detail]
      | .error e, _ => fails := fails ++ [s!"{id}: error '{e}'"]
      | _, .error e => fails := fails ++ [s!"{id}: cannot read expected output {e}"]
  let net ← unreached.get
  let netFails := fails.filter fun f => net.any (fun i => f.startsWith (i ++ ":"))
  skips := skips ++ netFails.map fun f => (f.splitOn ":").head! ++ " (needs the network)"
  fails := fails.filter fun f => !netFails.contains f
  for f in fails do IO.println s!"FAIL {f}"
  IO.println s!"{pass} pass, {fails.length} fail, {skips.length} skipped"
  pure (if fails.isEmpty then 0 else 1)
