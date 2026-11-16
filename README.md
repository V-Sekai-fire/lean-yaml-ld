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

Errors are strings that start with the specification's code: `mapping-key-error`, `profile-error`, or `loading-document-failed`, which covers text that is not YAML (the detail follows, as `syntax: ...`), a scalar root, a repeated key, an alias of no anchor and a cycle. `YamlLd.parseYaml` and `parseAllYaml` read any YAML value, with no rule on the root.

## What the specification asks, and where it is met

- A stream is UTF-8 (4.1.1), and holds documents (4.1.3, 4.4.1). The root of a document is a mapping, a sequence or null; a scalar root is `loading-document-failed`. A stream with none, or with only whitespace and comments, is null for `parse` and empty for `parseAll`.
- Anchors are copied where aliased and their names are dropped. An anchor that holds its own alias is a cycle and is refused (4.2.1, 4.3).
- Scalars resolve by the YAML Core Schema. `no`, `yes` and `on` are strings, and `2018-04-01` is a string. `.inf` and `.nan` are refused (4.3.1).
- Every mapping key is a string (4.4.2). A key may be explicit (`? `), carry an anchor or a tag, or be an alias, if it comes out a string. A mapping, a sequence, a number or an empty key is a `mapping-key-error`.
- Comments are whitespace. `%TAG` handles, `!<...>` verbatim tags and `!!` are expanded, so a tag in the yaml.org namespace is the Core Schema tag whatever it is spelt as. A tag of another namespace is ignored, as 4.3.1 gives it no meaning; a `!!` tag outside the Core Schema, and any directive but `%YAML 1.2` and `%TAG`, is a `profile-error`.
- A number keeps its digits: `100.0` stays `100.0` and `1.50` stays `1.50`.

JSON is YAML, so a JSON-LD file reads through it too.

## Checks

`./make.sh` builds and runs `yamlld_witness`. Its checks come in three kinds, and a check that can fail has a control that makes it:

- **GOLDEN**: the worked examples of the specification (1, 3, 4 and 7) read against the JSON the specification gives, and the Core Schema scalars, escapes and block scalars.
- **INVARIANT**: JSON reads as JSON; a comment, an anchor's name and key order change nothing; writing then reading gives the value back, for hard values and for every file in `tests/`.
- **CONTROL**: example 6 and the other inputs that must be refused, a changed expectation for each golden, and a file that is not UTF-8.

## The JSON-LD processor

`JsonLd` is a JSON-LD 1.1 processor in Lean: IRI resolution (RFC 3986), context processing, IRI expansion and the expansion algorithm, with scoped contexts, `@import`, `@nest`, `@reverse`, `@json`, index, id, type, language and graph maps, and protected terms. `JsonLd.expand` takes a `Lean.Json` document, a base IRI and a document loader. Compaction, flattening, RDF conversion and framing are not written yet, so this is not yet a conformant implementation in the sense of section 2.2.

## The W3C test suites

`jsonld_suite <tests-dir> <manifest>` runs the expand tests of a manifest (`./run-suite.sh` runs each test in its own process with a time limit). A negative test must give the manifest's error code, and a positive test must give the expected output, with arrays compared as sets except in `@list`. Other test kinds, HTML extraction, and tests of remote loading by HTTP are listed as skipped, never as passed.

| Manifest | Pass | Fail | Skipped |
| --- | --- | --- | --- |
| json-ld-api `expand-manifest.jsonld` | 368 | 0 | 18 |
| yaml-ld `manifest.jsonld` | 54 | 19 | 24 |

The 19 failures are the `core-*` tests of the YAML-LD suite. Each loads a context document that is a bare context (`"@vocab": ...`, with no `@context` key), which the JSON-LD API suite requires to be an `invalid remote context`. The two suites disagree, and this processor follows the JSON-LD API.

## What it does not have

- Tabs as indentation, and a block mapping on the line of `---`. Each is refused with an error, not read wrongly.
- JSON-LD processing. This reads YAML-LD into JSON; expansion, compaction and framing are not here.
- The YAML-LD Extended Profile.
- The writer lists keys sorted, because `Lean.Json` keeps them sorted. Key order is not data in YAML-LD.
- Expansion-level checks of the W3C suite. See below for what is run.

## Licence

MIT. See [LICENSE](LICENSE).
