import JsonLd
import YamlLd

/-! `jsonld_suite <tests-dir> <manifest.jsonld> [id-filter]`: run a JSON-LD test manifest (json-ld/json-ld-api or yaml-ld) against the processor.
Only the tests the processor implements are run; the others are listed as skipped, never as passed. -/

open Lean JsonLd

def testsPrefix : String := "https://w3c.github.io/json-ld-api/tests/"
def yamlPrefix : String := "https://w3c.github.io/yaml-ld/tests/"

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

def main (args : List String) : IO UInt32 := do
  let (dir, manifest, filter) ← match args with
    | [d, m] => pure (d, m, "")
    | [d, m, f] => pure (d, m, f)
    | _ => IO.eprintln "usage: jsonld_suite <tests-dir> <manifest.jsonld> [id-filter]"; return 2
  let loader : String → IO (Except String Json) := fun url => do
    let rel? := if url.startsWith testsPrefix then some (url.drop testsPrefix.length).toString
      else if url.startsWith yamlPrefix then some (url.drop yamlPrefix.length).toString else none
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
    if !kinds.contains "jld:ExpandTest" then skips := skips ++ [id ++ " (not an expand test)"]; continue
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
        match ← (((expand j (some base) ec).run { loader }).run : IO _) with
        | .ok (.arr a) => acc := acc ++ a
        | .ok x => acc := acc.push x
        | .error e => r := .error e; break
      if r.toOption.isSome then r := .ok (Json.arr acc)
    if isNeg then
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
  for f in fails do IO.println s!"FAIL {f}"
  IO.println s!"{pass} pass, {fails.length} fail, {skips.length} skipped"
  pure (if fails.isEmpty then 0 else 1)
