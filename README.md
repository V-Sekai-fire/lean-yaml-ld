# lean-yaml-ld

A reader and writer for [YAML-LD 1.0](https://www.w3.org/TR/yaml-ld/) in Lean 4, and a JSON-LD 1.1 processor to go with it. `YamlLd` turns a YAML-LD stream into `Lean.Json` and back; `JsonLd` expands, compacts, flattens, frames and converts to and from RDF. Neither has a dependency beyond Lean itself. The library reads no HTML and opens no sockets; both stay in the test runner (see below).

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

Expand a YAML-LD document with the processor. It takes a document loader as a callback, for remote contexts:

    import YamlLd
    import JsonLd
    open Lean

    def loader : String → IO (Except String Json) := fun _ => pure (.error "no loader")

    def main : IO Unit := do
      let .ok doc := YamlLd.parse "\"@context\": {\"@vocab\": \"http://example/\"}\nname: Ada\n" | return
      match ← ((JsonLd.expand doc (some "http://example/doc")).run { loader }).run with
      | .ok j => IO.println j.compress   -- [{"http://example/name":[{"@value":"Ada"}]}]
      | .error e => IO.println e

## Checks

`./make.sh` builds and runs `yamlld_witness`. Its checks come in three kinds, and a check that can fail has a control that makes it:

- **GOLDEN**: the worked examples of the specification (1, 3, 4 and 7) read against the JSON the specification gives, and the Core Schema scalars, escapes and block scalars.
- **INVARIANT**: JSON reads as JSON; a comment, an anchor's name and key order change nothing; writing then reading gives the value back, for hard values and for every file in `tests/`.
- **CONTROL**: example 6 and the other inputs that must be refused, a changed expectation for each golden, and a file that is not UTF-8.

## The JSON-LD processor

`JsonLd` is a JSON-LD 1.1 processor. Every function runs in `JsonLd.PM`, which carries a `Cfg` (the document loader) and fails with the JSON-LD API's error codes as strings.

| Function | What it does |
| --- | --- |
| `JsonLd.expand` | expansion: context processing, scoped contexts, `@import`, `@nest`, `@reverse`, `@json`, index, id, type, language and graph maps, protected terms |
| `JsonLd.flattenExpanded` | flattening, with blank node labels |
| `JsonLd.compactDoc` | compaction against a context; `CompOpts.graph` always wraps flattened nodes in `@graph` |
| `JsonLd.toRdfQuads` | N-Quads from an expanded document |
| `JsonLd.fromRdf` | JSON-LD from quads read by `JsonLd.parseNQuads` |
| `JsonLd.frameDoc` | framing |
| `JsonLd.Remote.load` | the document loader's decisions (redirects, the `Link` header, the content type) over any transport function |

The library reads no HTML and has no HTTP client. `HtmlScripts` (used only by the test runner) finds `<script>` elements and `<base href>` in an HTML file; the caller parses what it finds with `YamlLd` or `Lean.Json`. The test runner answers `JsonLd.Remote.load` from each test's options instead of a socket. Lean's standard library has no TLS client, so it fetches a network document with `curl`.

## The W3C test suites

`jsonld_suite <tests-dir> <manifest> [id]` runs the tests of a W3C manifest against the processor. `./run-suite.sh` runs each test in its own process with a time limit, so a hang is one failure. CI runs `./make.sh` and every manifest below, and fails on any failure. A negative test must give the manifest's error code, and a positive test must give the expected output, with arrays compared as sets except in `@list`; blank node labels are compared up to renaming. Set `JSONLD_SHOW_SKIPS` to list the skipped tests.

A skipped test is never counted as passed. What is skipped, and why:

- **JSON-LD 1.0 mode.** Tests with `processingMode` or `specVersion` `json-ld-1.0`: the processor is 1.1 only. This is all the skips in expand, fromRdf, flatten, compact and frame, and 19 of toRdf.
- **Syntax tests.** The 16 `PositiveSyntaxTest` tests in toRdf are not run: the runner has no check for that kind.
- **Extended Profile.** The 5 yaml-ld tests with `extendedYAML`.
- **A contradiction in the suite.** `tr006` in html expects empty output for an HTML file with no script; `te006` expects `loading document failed` for the same file. `te006` is run.
- **No network.** A test that names a document outside the suite (an `https://` context) is skipped if `curl` cannot fetch it. None is skipped in CI.

Where the specification text and a test disagree, the test wins: after a 303 redirect the document URL is the target's (`#t0006` in remote-doc).

| Manifest | Pass | Fail | Skipped |
| --- | --- | --- | --- |
| json-ld-api `expand-manifest.jsonld` | 368 | 0 | 18 |
| json-ld-api `toRdf-manifest.jsonld` | 432 | 0 | 35 |
| json-ld-api `fromRdf-manifest.jsonld` | 53 | 0 | 1 |
| json-ld-api `flatten-manifest.jsonld` | 55 | 0 | 3 |
| json-ld-api `compact-manifest.jsonld` | 233 | 0 | 13 |
| json-ld-api `html-manifest.jsonld` | 49 | 0 | 1 |
| json-ld-api `remote-doc-manifest.jsonld` | 18 | 0 | 0 |
| json-ld-framing `frame-manifest.jsonld` | 73 | 0 | 19 |
| yaml-ld `manifest.jsonld` | 92 | 0 | 5 |

Where YAML-LD and JSON-LD disagree, YAML-LD wins, for documents read from a YAML-LD file (`.yamlld`, `.yaml`): a context document may be a bare context with no `@context` entry (`Cfg.bareContext`), and a top-level node whose properties were all null keeps its `@id` (`ExpOpts.keepIdOnly`). JSON-LD documents follow the JSON-LD API as before.

## What it does not have

- Tabs as indentation, and a block mapping on the line of `---`. Each is refused with an error, not read wrongly.
- The YAML-LD Extended Profile.
- JSON-LD 1.0 processing mode.
- HTML extraction and an HTTP client in the library. They belong to the caller, who passes a document loader.
- The writer lists keys sorted, because `Lean.Json` keeps them sorted. Key order is not data in YAML-LD.
- A claim of conformance in the sense of section 2.2 of YAML-LD 1.0. The suites above pass except for the skips listed, but nobody outside this repository has reviewed that.

## Licence

MIT. See [LICENSE](LICENSE).
