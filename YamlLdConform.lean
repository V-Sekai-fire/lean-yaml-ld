import YamlLd

/-! `yamlld_conform first|all <file>`: print the document(s) of a file as compact JSON, one per line, or the error and exit 1.
Used by `tests/conformance.py` to run the W3C YAML-LD test manifest. -/

open Lean

def main (args : List String) : IO UInt32 := do
  match args with
  | [mode, path] =>
    match ← YamlLd.readText path with
    | .error e => IO.println e; pure 1
    | .ok t =>
      let r := if mode == "all" then YamlLd.parseAll t else (fun d => #[d]) <$> YamlLd.parse t
      match r with
      | .ok ds => for d in ds do IO.println d.compress
                  pure 0
      | .error e => IO.println e; pure 1
  | _ => IO.eprintln "usage: yamlld_conform first|all <file>"; pure 2
