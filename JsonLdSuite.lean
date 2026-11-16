import JsonLd
import YamlLd

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

def readDocs (path : String) (all : Bool) : IO (Except String (Array Json)) := do
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
  let loader : String → IO (Except String Json) := fun url => do
    let rel? := if url.startsWith testsPrefix then some (url.drop testsPrefix.length).toString
      else if url.startsWith yamlPrefix then some (url.drop yamlPrefix.length).toString
      else if url.startsWith framingPrefix then some (url.drop framingPrefix.length).toString else none
    match rel? with
    | some rel => readDoc (dir ++ "/" ++ rel)
    | none => pure (.error s!"no such document {url}")
  let some mtext ← (do match ← YamlLd.readText manifest with | .ok t => pure (some t) | .error _ => pure none) | IO.eprintln "no manifest"; return 2
  let .ok m := Json.parse mtext | IO.eprintln "bad manifest"; return 2
  let mut pass := 0
  let mut fails : List String := []
  let mut skips : List String := []
  for t in arrayify ((get? m "sequence").getD Json.null) do
    let id := ((get? t "@id").bind asStr?).getD ""
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
    if has opts "contentType" || has opts "redirectTo" || has opts "httpLink" || get? opts "processingMode" == some (Json.str "json-ld-1.0")
        || get? opts "specVersion" == some (Json.str "json-ld-1.0") || has opts "extendedYAML" then
      skips := skips ++ [id ++ " (option)"]; continue
    let some input := (get? t "input").bind asStr? | skips := skips ++ [id]; continue
    if input.endsWith ".html" then skips := skips ++ [id ++ " (HTML)"]; continue
    let isNeg := kinds.contains "jld:NegativeEvaluationTest"
    let docUrl := (if input.startsWith "cases/" && manifest.contains "yaml" then yamlPrefix else testsPrefix) ++ input
    let base := ((get? opts "base").bind asStr?).getD docUrl
    let ec ← match (get? opts "expandContext").bind asStr? with
      | some p => do match ← readDoc (dir ++ "/" ++ p) with | .ok j => pure (some j) | .error _ => pure none
      | none => pure none
    let all := get? opts "extractAllScripts" == some (Json.bool true)
    let docs ← readDocs (dir ++ "/" ++ input) all
    let mut r : Except String Json := .ok (Json.arr #[])
    match docs with
    | .error e => r := .error e
    | .ok js =>
      let mut acc : Array Json := #[]
      for j in js do
        match ← (((expandWith j (some base) ec { keepIdOnly := input.endsWith ".yamlld" || input.endsWith ".yaml" }).run { loader, bareContext := fun u => u.endsWith ".yamlld" || u.endsWith ".yaml" }).run : IO _) with
        | .ok (.arr a) => acc := acc ++ a
        | .ok x => acc := acc.push x
        | .error e => r := .error e; break
      if r.toOption.isSome then r := .ok (Json.arr acc)
    let copts : CompOpts := { compactArrays := get? opts "compactArrays" != some (Json.bool false),
                              relative := get? opts "compactToRelative" != some (Json.bool false) }
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
  for f in fails do IO.println s!"FAIL {f}"
  IO.println s!"{pass} pass, {fails.length} fail, {skips.length} skipped"
  pure (if fails.isEmpty then 0 else 1)
