import YamlLd
/-! Converts a JSON-LD file to a YAML-LD file and checks that the YAML-LD reads back to the same JSON value, so that the two
documents mean the same (YAML-LD 1.0 is JSON-LD in YAML).
usage: jsonld_to_yamlld to <in.jsonld> <out.yamlld>      write the YAML-LD file and read it back
       jsonld_to_yamlld from <in.yamlld> <out.jsonld>    read a YAML-LD file and write its JSON, compact
Exit status 0 only when the file was converted and, for `to`, reads back equal. -/
open Lean

def toYaml (src dst : String) : IO UInt32 := do
  let text ← IO.FS.readFile src
  match Json.parse text with
  | .error e => IO.eprintln s!"{src}: not JSON: {e}"; return 1
  | .ok j =>
    let y := YamlLd.render j
    IO.FS.writeFile dst y
    match YamlLd.parse y with
    | .error e => IO.eprintln s!"{dst}: does not read back: {e}"; return 1
    | .ok j2 =>
      if j2 == j then
        IO.println s!"{src} -> {dst}: reads back equal"
        return 0
      else
        IO.eprintln s!"{dst}: reads back DIFFERENT from {src}"
        return 1

def fromYaml (src dst : String) : IO UInt32 := do
  match ← YamlLd.readFile src with
  | .error e => IO.eprintln s!"{src}: {e}"; return 1
  | .ok j => IO.FS.writeFile dst (j.compress ++ "\n"); IO.println s!"{src} -> {dst}"; return 0

def main (args : List String) : IO UInt32 :=
  match args with
  | ["to", src, dst] => toYaml src dst
  | ["from", src, dst] => fromYaml src dst
  | _ => do IO.eprintln "usage: jsonld_to_yamlld to|from <in> <out>"; return 2
