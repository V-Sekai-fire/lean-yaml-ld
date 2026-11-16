# lean-yaml-ld

A reader and writer for [YAML-LD 1.0](https://www.w3.org/TR/yaml-ld/) in Lean 4. It turns a YAML-LD stream into `Lean.Json` and back. It has no dependency beyond Lean itself.

## Use it

Add it to a `lakefile.lean`:

    require «lean-yaml-ld» from git "https://github.com/V-Sekai-fire/lean-yaml-ld" @ "main"

Then:

    import YamlLd
    open Lean

    #eval YamlLd.parse "a: [no, 2018-04-01, 1.50]\n"   -- {"a": ["no", "2018-04-01", 1.50]}
    #eval IO.println (YamlLd.render (Json.mkObj [("a", Json.str "yes")]))

| Function | What it does |
| --- | --- |
| `YamlLd.parse` | the first document of a stream (`extractAllScripts` false) |
| `YamlLd.parseAll` | every document, in order (`extractAllScripts` true) |
| `YamlLd.render` | a JSON value as a block-style YAML-LD document |
| `YamlLd.readFile` | the first document of a file; a file that is not UTF-8 is refused |

Errors are strings that start with the specification's code: `mapping-key-error`, `profile-error`, `loading-document-failed`, or `syntax-error` for text that is not YAML.

## What the specification asks, and where it is met

- A stream is UTF-8 (4.1.1), and holds one or more documents (4.1.3, 4.4.1).
- Anchors are copied where aliased and their names are dropped. An anchor that holds its own alias is a cycle and is refused (4.2.1, 4.3).
- Scalars resolve by the YAML Core Schema. `no`, `yes` and `on` are strings, and `2018-04-01` is a string. `.inf` and `.nan` are refused (4.3.1).
- Every mapping key is a string (4.4.2). A key may be explicit (`? `), carry an anchor or a tag, or be an alias, if it comes out a string. A mapping, a sequence, a number or an empty key is a `mapping-key-error`.
- Comments are whitespace. `%TAG` handles, `!<...>` verbatim tags and `!!` are expanded, so a tag in the yaml.org namespace is the Core Schema tag whatever it is spelt as. A tag outside the Core Schema, and any directive but `%YAML 1.2` and `%TAG`, is a `profile-error`.
- A number keeps its digits: `100.0` stays `100.0` and `1.50` stays `1.50`.

JSON is YAML, so a JSON-LD file reads through it too.

## Checks

`./make.sh` builds and runs `yamlld_witness`. Its checks come in three kinds, and a check that can fail has a control that makes it:

- **GOLDEN**: the worked examples of the specification (1, 3, 4 and 7) read against the JSON the specification gives, and the Core Schema scalars, escapes and block scalars.
- **INVARIANT**: JSON reads as JSON; a comment, an anchor's name and key order change nothing; writing then reading gives the value back, for hard values and for every file in `tests/`.
- **CONTROL**: example 6 and the other inputs that must be refused, a changed expectation for each golden, and a file that is not UTF-8.

## What it does not have

- Tabs as indentation, and a block mapping on the line of `---`. Each is refused with an error, not read wrongly.
- JSON-LD processing. This reads YAML-LD into JSON; expansion, compaction and framing are not here.
- The YAML-LD Extended Profile.
- The writer lists keys sorted, because `Lean.Json` keeps them sorted. Key order is not data in YAML-LD.
- A run against the W3C YAML-LD test suite. The checks here are the specification's examples and the cases listed above.

## Licence

MIT. See [LICENSE](LICENSE).
