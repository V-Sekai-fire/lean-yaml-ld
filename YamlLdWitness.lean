import YamlLd

/-! Checks for the YAML-LD reader and writer. Each is run on the real thing and, where it can fail, on a planted fault that it must catch.
The GOLDEN checks are the worked examples of the YAML-LD specification (https://www.w3.org/TR/yaml-ld/) read against the JSON the specification gives for them.
The INVARIANT checks hold for any document: JSON reads the same as JSON, a comment changes nothing, writing then reading gives the value back.
The CONTROL checks are inputs that must be refused, and changed expectations that must not be equal.
usage: yamlld_witness <file.yamlld>...   (each file is also written and read back) -/

open Lean

structure Check where
  name : String
  ok : Bool

/-- Any YAML value; the YAML-LD rule on the root is checked on its own, with `ld`. -/
def y (t : String) : Except String Json := YamlLd.parseYaml t

def ld (t : String) : Except String Json := YamlLd.parse t

def j (t : String) : Json := (Json.parse t).toOption.getD Json.null

/-- Reading the YAML-LD gives this JSON. -/
def reads (t expected : String) : Bool :=
  match y t with
  | .ok v => v == j expected
  | .error _ => false

/-- Reading is refused with this error code. -/
def refused (t code : String) : Bool :=
  match y t with
  | .ok _ => false
  | .error e => e.startsWith code

def ex1 : String := "\"@context\":
  schema: https://schema.org/
  dbo: http://dbpedia.org/ontology/
  dbp: http://dbpedia.org/property/
  dbr: http://dbpedia.org/resource/
  xsd: http://www.w3.org/2001/XMLSchema#
  dbp:discovered:
    \"@type\": xsd:date
  dbp:star:
    \"@type\": \"@id\"

\"@id\": dbr:Proxima_Centauri_b
\"@type\": dbo:Planet
schema:description: >-
  The closest known exoplanet to Earth,
  orbiting in Proxima Centauri's habitable zone.
dbp:discovered: 2016-08-24
dbp:star: dbr:Proxima_Centauri
"

def ex2 : String := "{
  \"@context\": {
    \"schema\": \"https://schema.org/\",
    \"dbo\": \"http://dbpedia.org/ontology/\",
    \"dbp\": \"http://dbpedia.org/property/\",
    \"dbr\": \"http://dbpedia.org/resource/\",
    \"xsd\": \"http://www.w3.org/2001/XMLSchema#\",
    \"dbp:discovered\": { \"@type\": \"xsd:date\" },
    \"dbp:star\": { \"@type\": \"@id\" }
  },
  \"@id\": \"dbr:Proxima_Centauri_b\",
  \"@type\": \"dbo:Planet\",
  \"schema:description\": \"The closest known exoplanet to Earth, orbiting in Proxima Centauri's habitable zone.\",
  \"dbp:discovered\": \"2016-08-24\",
  \"dbp:star\": \"dbr:Proxima_Centauri\"
}"

def ex3 : String := "\"@context\":
  dbo: http://dbpedia.org/ontology/
  dbr: http://dbpedia.org/resource/
\"@id\": dbr:Proxima_Centauri
\"@type\": dbo:Star
---
\"@context\":
  dbo: http://dbpedia.org/ontology/
  dbr: http://dbpedia.org/resource/
\"@id\": dbr:Proxima_Centauri_b
\"@type\": dbo:Planet
"

def ex4 : String := "\"@context\":
  dbo: http://dbpedia.org/ontology/
  dbp: http://dbpedia.org/property/
  dbr: http://dbpedia.org/resource/

  dbp:star:            &iri
    \"@type\": \"@id\"
  dbp:discoveryMethod: *iri
  dbp:discoverySite:   *iri

\"@id\": dbr:Proxima_Centauri_b
dbp:star:            dbr:Proxima_Centauri
dbp:discoveryMethod: dbr:Doppler_spectroscopy
dbp:discoverySite:   dbr:European_Southern_Observatory
"

def ex5 : String := "{
  \"@context\": {
    \"dbo\": \"http://dbpedia.org/ontology/\",
    \"dbp\": \"http://dbpedia.org/property/\",
    \"dbr\": \"http://dbpedia.org/resource/\",
    \"dbp:star\": { \"@type\": \"@id\" },
    \"dbp:discoveryMethod\": { \"@type\": \"@id\" },
    \"dbp:discoverySite\": { \"@type\": \"@id\" }
  },
  \"@id\": \"dbr:Proxima_Centauri_b\",
  \"dbp:star\": \"dbr:Proxima_Centauri\",
  \"dbp:discoveryMethod\": \"dbr:Doppler_spectroscopy\",
  \"dbp:discoverySite\": \"dbr:European_Southern_Observatory\"
}"

def ex6 : String := "\"@context\":
  - https://json-ld.org/contexts/dollar-convenience.jsonld
  - dbo: http://dbpedia.org/ontology/
    dbp:star: &iri
      \"@type\": \"@id\"

{ $id: dbr:Proxima_Centauri_b, $type: dbo:Planet, dbp:star: dbr:Proxima_Centauri }:
  dbp:discovered: 2016-08-24
"

def ex7 : String := "\"@context\":
  schema: https://schema.org/
  dbr: http://dbpedia.org/resource/

\"@id\": dbr:Proxima_Centauri_b
schema:additionalProperty:
  \"@type\": \"@json\"
  \"@value\":
    semiMajorAxis: 0.0485
    orbitalPeriod: 11.186
    equilibriumTemperature: 234
    eccentricity: 0.11
"

def ex7json : String := "{\"@context\":{\"schema\":\"https://schema.org/\",\"dbr\":\"http://dbpedia.org/resource/\"},
 \"@id\":\"dbr:Proxima_Centauri_b\",\"schema:additionalProperty\":{\"@type\":\"@json\",
 \"@value\":{\"semiMajorAxis\":0.0485,\"orbitalPeriod\":11.186,\"equilibriumTemperature\":234,\"eccentricity\":0.11}}}"

/-- JSON texts: each is YAML too, and must read as the JSON does. -/
def jsonSamples : List String :=
  [ "{\"a\":1,\"b\":[true,false,null,\"x\"],\"c\":{\"d\":-2.5,\"e\":1e3,\"f\":\"\"}}",
    "[1, 2.50, \"three\", [], {}, [[]], {\"k\": {}}]",
    "{\"text\": \"tab\\there\\nnewline \\\"q\\\" \\\\ \\u00e9 \\u2713\", \"uni\": \"é✓\"}",
    "{\"@context\":{\"VSEKAI\":\"https://v-sekai.org/\"},\"@type\":\"domain:Plan\",\"steps\":[{\"action\":\"encode-packets\",\"params\":[],\"duration\":\"PT0S\"}]}",
    "\"just a string\"", "42", "null" ]

/-- Values that are hard to write as plain scalars: each must come back as itself. -/
def hard : List Json :=
  [ j "\"\"", j "\"yes\"", j "\"no\"", j "\"null\"", j "\"~\"", j "\"true\"", j "\"123\"", j "\"1.5\"", j "\"0x1F\"",
    j "\"2018-04-01\"", j "\" leading\"", j "\"trailing \"", j "\"a: b\"", j "\"a #b\"", j "\"ends:\"", j "\"- dash\"",
    j "\"@context\"", j "\"# hash\"", j "\"line\\nbreak\"", j "\"tab\\there\"", j "\"é✓ unicode\"", j "\"quote \\\" mark\"",
    j "\"back \\\\ slash\"", j "\"[flow]\"", j "\"{flow}\"", j "\"*star\"", j "\"&amp\"", j "\"!bang\"", j "\"%pct\"",
    j "{\"\":1,\"a b\":2,\"@id\":3,\"1\":4,\"true\":5,\"x: y\":6}",
    j "[[],{},[[]],[{}],{\"a\":[]},{\"a\":{}}]",
    j "[1,-2,3.5,100.0,0.0485,1.50,true,false,null]",
    j "{\"a\":[{\"b\":[1,[2,{\"c\":null}]]},[[3]]]}" ]

def roundTrips (v : Json) : Bool :=
  match y (YamlLd.render v) with
  | .ok w => w == v
  | .error _ => false

def main (args : List String) : IO UInt32 := do
  let mut files : List (String × Json) := []
  for f in args do
    match ← YamlLd.readFile f with
    | .ok v => files := files ++ [(f, v)]
    | .error e => IO.eprintln s!"cannot read: {e}"; return 3
  let spaced := "a: 1 # one\n# a line of comment\nb: [1, 2] # two\n\nc:\n  # inside\n  d: x\n"
  let bare := "a: 1\nb: [1, 2]\n\nc:\n  d: x\n"
  let allOk := fun (p : Json → Bool) => files.all fun (_, v) => p v
  let fileCheck (name : String) (p : Json → Bool) : List Check :=
    if files.isEmpty then [] else [{ name, ok := allOk p }]
  let checks : List Check :=
    [ -- GOLDEN: the examples of the specification
      { name := "GOLDEN example 1 (the introductory document) reads as the JSON of example 2; the date stays a string", ok := reads ex1 ex2 },
      { name := "CONTROL a changed date is not the JSON of example 2", ok := !(reads (ex1.replace "2016-08-24" "2016-08-25") ex2) },
      { name := "GOLDEN example 3: a stream of two documents gives two, and `parse` takes the first",
        ok := (match YamlLd.parseAll ex3 with
               | .ok ds => ds.size == 2 && ((y ex3).toOption == ds[0]?)
                 && ds[1]? == some (j "{\"@context\":{\"dbo\":\"http://dbpedia.org/ontology/\",\"dbr\":\"http://dbpedia.org/resource/\"},\"@id\":\"dbr:Proxima_Centauri_b\",\"@type\":\"dbo:Planet\"}")
               | .error _ => false) },
      { name := "CONTROL a stream of one document still gives an array of one", ok := (match YamlLd.parseAll ex1 with | .ok ds => ds.size == 1 | .error _ => false) },
      { name := "GOLDEN example 4: an anchored context term, aliased twice, reads as example 5", ok := reads ex4 ex5 },
      { name := "CONTROL an alias that is not the anchored value is not example 5", ok := !(reads (ex4.replace "dbp:discoverySite:   *iri" "dbp:discoverySite:   x") ex5) },
      { name := "GOLDEN example 7: a @json literal keeps its object and its numbers", ok := reads ex7 ex7json },
      { name := "CONTROL a changed number in the literal is not the same JSON", ok := !(reads (ex7.replace "11.186" "11.187") ex7json) },
      -- CONTROL: what the specification refuses
      { name := "CONTROL example 6: a mapping used as a key is a mapping-key-error", ok := refused ex6 "mapping-key-error" },
      { name := "CONTROL a number as a key is a mapping-key-error", ok := refused "1: a\n" "mapping-key-error" },
      { name := "CONTROL a boolean as a key is a mapping-key-error", ok := refused "true: a\n" "mapping-key-error" },
      { name := "CONTROL a null as a key is a mapping-key-error", ok := refused "~: a\n" "mapping-key-error" },
      { name := "CONTROL an unquoted @context key is refused: @ is reserved, so the key must be quoted", ok := refused "@context: x\n" "loading-document-failed" && reads "\"@context\": x\n" "{\"@context\":\"x\"}" },
      { name := "CONTROL a quoted number as a key is fine", ok := reads "\"1\": a\n" "{\"1\":\"a\"}" },
      { name := "CONTROL .inf, -.inf and .nan are refused (no JSON form)",
        ok := refused "a: .inf\n" "loading-document-failed" && refused "a: -.inf\n" "loading-document-failed" && refused "a: .nan\n" "loading-document-failed" },
      { name := "CONTROL an alias of no anchor is refused", ok := refused "a: *nope\n" "loading-document-failed" },
      { name := "CONTROL an anchor that holds its own alias is a cycle and is refused", ok := refused "a: &x [*x]\n" "loading-document-failed" },
      { name := "CONTROL a key given twice is refused", ok := refused "a: 1\na: 2\n" "loading-document-failed" },
      { name := "CONTROL a tag outside the Core Schema is a profile-error", ok := refused "a: !!timestamp 2018-04-01\n" "profile-error" && refused "a: !ex:thing x\n" "profile-error" },
      { name := "CONTROL a %YAML 1.1 directive is a profile-error", ok := refused "%YAML 1.1\n---\na: 1\n" "profile-error" },
      { name := "CONTROL a directive other than %YAML and %TAG is a profile-error", ok := refused "%FOO bar\n---\na: 1\n" "profile-error" },
      -- GOLDEN: the gaps of the first version, now met
      { name := "GOLDEN a complex key (? ) that is a string, with its value on a line of its own, or none", ok := reads "? a\n: 1\n? \"b c\"\n: [x]\n? d\ne: 2\n" "{\"a\":1,\"b c\":[\"x\"],\"d\":null,\"e\":2}" },
      { name := "GOLDEN a complex key that is a block scalar, and a nested mapping with complex keys", ok := reads "? |-\n  multi\n  line\n: 1\nm:\n  ? k\n  : v\n" "{\"multi\\nline\":1,\"m\":{\"k\":\"v\"}}" },
      { name := "CONTROL a complex key that is a mapping, a sequence, a number or empty is a mapping-key-error",
        ok := refused "? {a: 1}\n: x\n" "mapping-key-error" && refused "? - a\n: x\n" "mapping-key-error" && refused "? 1\n: x\n" "mapping-key-error" && refused "?\n: x\n" "mapping-key-error" },
      { name := "GOLDEN ? in a flow mapping and a flow sequence", ok := reads "{? a : 1, ? b}\n" "{\"a\":1,\"b\":null}" && reads "[? a : 1, ? b]\n" "[{\"a\":1},{\"b\":null}]" },
      { name := "GOLDEN an anchor on a key, and an alias of it as a value", ok := reads "&k a: 1\nb: *k\n" "{\"a\":1,\"b\":\"a\"}" },
      { name := "GOLDEN an alias as a key", ok := reads "x: &k name\n*k : 1\n" "{\"x\":\"name\",\"name\":1}" },
      { name := "CONTROL an alias of a non-string as a key is a mapping-key-error", ok := refused "x: &n 5\n*n : 1\n" "mapping-key-error" },
      { name := "GOLDEN a tag on a key: !!str 1 is the string key 1; a sequence entry may start with a tagged key", ok := reads "!!str 1: a\n" "{\"1\":\"a\"}" && reads "- !!str 2: b\n" "[{\"2\":\"b\"}]" },
      { name := "CONTROL a tag that makes a key a non-string is a mapping-key-error; a tag outside the Core Schema is a profile-error", ok := refused "!!int 1: a\n" "mapping-key-error" && refused "!ex:t k: a\n" "profile-error" },
      { name := "GOLDEN %TAG: a handle that names the Core Schema reads as it", ok := reads "%TAG !e! tag:yaml.org,2002:\n---\na: !e!str 5\nb: !e!int 7\n" "{\"a\":\"5\",\"b\":7}" },
      { name := "GOLDEN %TAG may redefine !! and ! ; a verbatim !<tag:yaml.org,2002:str> is !!str", ok := reads "%TAG !! tag:yaml.org,2002:\n---\na: !!str 5\n" "{\"a\":\"5\"}" && reads "a: !<tag:yaml.org,2002:str> 5\nb: !<tag:yaml.org,2002:int> 5\n" "{\"a\":\"5\",\"b\":5}" },
      { name := "CONTROL %TAG: a handle that names another namespace is a profile-error; an undeclared handle, a repeated one and a bad one are syntax-errors",
        ok := refused "%TAG !e! tag:example.com,2000:\n---\na: !e!x 1\n" "profile-error" && refused "a: !e!str 1\n" "loading-document-failed"
          && refused "%TAG !e! x:\n%TAG !e! y:\n---\na: 1\n" "loading-document-failed" && refused "%TAG e x:\n---\na: 1\n" "loading-document-failed" && refused "%TAG !e!\n---\na: 1\n" "loading-document-failed" },
      { name := "CONTROL a %TAG holds for its document only: the next document has no such handle", ok := refused "%TAG !e! tag:yaml.org,2002:\n---\na: !e!str 5\n...\n---\nb: !e!str 5\n" "loading-document-failed" && (match YamlLd.parse "%TAG !e! tag:yaml.org,2002:\n---\na: !e!str 5\n" with | .ok _ => true | .error _ => false) },
      { name := "CONTROL a tab as indentation is refused", ok := refused "a:\n\tb: 1\n" "loading-document-failed" },
      { name := "CONTROL a badly indented entry is refused", ok := refused "a:\n  b: 1\n c: 2\n" "loading-document-failed" },
      { name := "CONTROL an unclosed quote is refused", ok := refused "a: \"open\n" "loading-document-failed" },
      { name := "CONTROL an unclosed flow sequence is refused", ok := refused "a: [1, 2\n" "loading-document-failed" },
      { name := "CONTROL a mapping on the line of its key is refused", ok := refused "a: b: c\n" "loading-document-failed" },
      { name := "GOLDEN a stream with no document, or only whitespace or comments, is null for `parse` and empty for `parseAll`",
        ok := (ld "# nothing\n").toOption == some Json.null && (ld "").toOption == some Json.null && (ld "  \n\n").toOption == some Json.null
          && (match YamlLd.parseAll "# nothing\n" with | .ok ds => ds.isEmpty | .error _ => false) },
      { name := "GOLDEN the root of a document is a mapping, a sequence or null", ok := (ld "a: 1\n").toOption.isSome && (ld "[1]\n").toOption.isSome && (ld "~\n").toOption == some Json.null },
      { name := "CONTROL a scalar root is loading-document-failed (4.1.3): a string, number, boolean or quoted null, in `parse` and `parseAll`",
        ok := ["text", "42", "1.5", "true", "\"null\"", "\"~\"", "---\nx\n---\na: 1\n"].all (fun d => (match ld d with | .error e => e.startsWith "loading-document-failed" | .ok _ => false)
                  || (match YamlLd.parseAll d with | .error e => e.startsWith "loading-document-failed" | .ok _ => false)) },
      { name := "CONTROL the same scalar root is a value to `parseYaml`, which has no such rule", ok := (y "42\n").toOption == some (j "42") },
      { name := "GOLDEN properties on the line after a key belong to its value: an anchor on a scalar below its key, and an alias of it",
        ok := reads "a:\n  &x \"v\"\nb:\n  *x\n" "{\"a\":\"v\",\"b\":\"v\"}" },
      { name := "GOLDEN properties on the line after a key, before a key, belong to that key", ok := reads "m:\n  &k a: 1\n  b: *k\n" "{\"m\":{\"a\":1,\"b\":\"a\"}}" },
      { name := "CONTROL an anchor above a mapping is the mapping's: an alias inside it is a cycle", ok := refused "&m\na: *m\n" "loading-document-failed" },
      -- GOLDEN: the Core Schema
      { name := "GOLDEN no, yes, on, off, y and NO are strings, not booleans (the Norway problem)",
        ok := reads "a: [no, yes, on, off, y, n, NO, Yes]\n" "{\"a\":[\"no\",\"yes\",\"on\",\"off\",\"y\",\"n\",\"NO\",\"Yes\"]}" },
      { name := "GOLDEN true, True, FALSE and null, Null, ~ are the booleans and null; a trailing comma adds no entry",
        ok := reads "a: [true, True, FALSE, null, Null, ~]\n" "{\"a\":[true,true,false,null,null,null]}" },
      { name := "GOLDEN a timestamp is a string, as 4.3.1 requires", ok := reads "a: 2018-04-01\nb: 2001-12-14t21:59:43.10-05:00\n" "{\"a\":\"2018-04-01\",\"b\":\"2001-12-14t21:59:43.10-05:00\"}" },
      { name := "GOLDEN numbers: 0o17 is 15, 0x1F is 31, -12, +3, 010 is 10, .5, 5., 1e3, 2.5E-2",
        ok := reads "a: [0o17, 0x1F, -12, +3, 010, .5, 5., 1e3, 2.5E-2]\n" "{\"a\":[15,31,-12,3,10,0.5,5,1000,0.025]}" },
      { name := "CONTROL 1_000, 1.2.3, 0b1, 0o8, 0xG, 1e and -  are strings",
        ok := reads "a: [1_000, 1.2.3, 0b1, 0o8, 0xG, 1e, \"-\"]\n" "{\"a\":[\"1_000\",\"1.2.3\",\"0b1\",\"0o8\",\"0xG\",\"1e\",\"-\"]}" },
      { name := "GOLDEN a number keeps its digits: 100.0 stays 100.0 and 1.50 stays 1.50, so a double is not made an integer", ok := reads "a: [100.0, 1.50, 0.0485]\n" "{\"a\":[100.0,1.50,0.0485]}" && YamlLd.render (j "[100.0,1.50,0.0485,-0.5,7]") == "- 100.0\n- 1.50\n- 0.0485\n- -0.5\n- 7\n" },
      { name := "CONTROL 100.0 is not 100 for the writer or the reader", ok := YamlLd.render (j "100.0") != YamlLd.render (j "100") && (y "100.0\n").toOption != (y "100\n").toOption },
      { name := "GOLDEN tags force the type: !!str 123 is a string, !!int 7 an integer, ! x a string", ok := reads "a: !!str 123\nb: !!int 7\nc: ! 5\nd: !!float 1.5\n" "{\"a\":\"123\",\"b\":7,\"c\":\"5\",\"d\":1.5}" },
      { name := "CONTROL a tag that the text does not fit is refused", ok := refused "a: !!int seven\n" "loading-document-failed" },
      -- GOLDEN: scalars
      { name := "GOLDEN a comment is whitespace; a # inside a word is not a comment; a URL with : and # is one string",
        ok := reads "a: b#c\nu: http://x.org/p#f\nz: 1 # gone\n" "{\"a\":\"b#c\",\"u\":\"http://x.org/p#f\",\"z\":1}" },
      { name := "GOLDEN double-quoted escapes: \\t \\n \\\" \\\\ \\x41 \\u00e9 \\U0001F600 and a folded line",
        ok := (y "a: \"t\\tn\\nq\\\"b\\\\ \\x41\\u00e9\\U0001F600\"\nb: \"one\n  two\n\n  three\"\n").toOption ==
          some (Json.mkObj [("a", Json.str ("t\tn\nq\"b\\ A\u00e9" ++ (Char.ofNat 0x1F600).toString)), ("b", Json.str "one two\nthree")]) },
      { name := "GOLDEN single quotes: '' is one quote and nothing else is an escape", ok := reads "a: 'it''s \\n here'\n" "{\"a\":\"it's \\\\n here\"}" },
      { name := "GOLDEN a plain scalar over several lines folds to one", ok := reads "a: one\n  two\n\n  three\nb: x\n" "{\"a\":\"one two\\nthree\",\"b\":\"x\"}" },
      { name := "GOLDEN a literal block keeps its breaks: clip, strip and keep",
        ok := reads "a: |\n  x\n  y\n\nb: |-\n  x\n\nc: |+\n  x\n\nd: 1\n" "{\"a\":\"x\\ny\\n\",\"b\":\"x\",\"c\":\"x\\n\\n\",\"d\":1}" },
      { name := "GOLDEN a folded block joins its lines, keeps a blank line and a more-indented line",
        ok := reads "a: >\n  one\n  two\n\n  three\n    more\n  four\n" "{\"a\":\"one two\\nthree\\n  more\\nfour\\n\"}" },
      { name := "GOLDEN an indentation indicator keeps leading spaces: |2", ok := reads "a: |2\n    x\n   y\n" "{\"a\":\"  x\\n y\\n\"}" },
      -- GOLDEN: collections
      { name := "GOLDEN a sequence at the indent of its key, a sequence of mappings and of sequences",
        ok := reads "a:\n- 1\n- x: 1\n  y: 2\n- - 3\n  - 4\nb: 2\n" "{\"a\":[1,{\"x\":1,\"y\":2},[3,4]],\"b\":2}" },
      { name := "GOLDEN a flow mapping with a sequence, a quoted key joined to its value and a missing value",
        ok := reads "a: {b: [1, 2, {c: d}], \"e\":f, g}\n" "{\"a\":{\"b\":[1,2,{\"c\":\"d\"}],\"e\":\"f\",\"g\":null}}" },
      { name := "GOLDEN a document with --- and ... markers, and a %YAML 1.2 directive", ok := reads "%YAML 1.2\n---\na: 1\n...\n" "{\"a\":1}" },
      { name := "GOLDEN a byte-order mark and CRLF line ends read as the document does", ok := reads "\uFEFFa: 1\r\nb:\r\n  - x\r\n" "{\"a\":1,\"b\":[\"x\"]}" },
      { name := "GOLDEN an empty value is null, and an empty document is null", ok := reads "a:\nb: 1\n" "{\"a\":null,\"b\":1}" && reads "---\n" "null" },
      -- INVARIANT
      { name := "INVARIANT JSON is YAML: every JSON sample reads as the JSON parser reads it", ok := jsonSamples.all fun t => reads t t },
      { name := "CONTROL a JSON sample with one value changed does not read as the original", ok := !(reads "{\"a\":1}" "{\"a\":2}") },
      { name := "INVARIANT a comment is whitespace: the document with comments reads as the one without", ok := (y spaced).toOption == (y bare).toOption && (y bare).toOption.isSome },
      { name := "CONTROL a changed value is not the same document", ok := (y (bare.replace "x" "z")).toOption != (y bare).toOption },
      { name := "INVARIANT an anchor's name is not data: renaming it changes nothing", ok := (y ex4).toOption == (y (ex4.replace "iri" "other")).toOption && (y ex4).toOption.isSome },
      { name := "INVARIANT an alias is a copy: each use reads as the anchored value", ok := reads "a: &v {k: 1}\nb: *v\nc: [*v, *v]\n" "{\"a\":{\"k\":1},\"b\":{\"k\":1},\"c\":[{\"k\":1},{\"k\":1}]}" },
      { name := "INVARIANT the order of keys is not data: two orders read as one document", ok := (y "a: 1\nb: 2\n").toOption == (y "b: 2\na: 1\n").toOption && (y "a: 1\nb: 2\n").toOption.isSome },
      { name := "INVARIANT writing then reading gives the value back, for each hard value (a string that looks like another type, a quote, a tab, a break)",
        ok := hard.all roundTrips },
      { name := "CONTROL a string that looks like a number, a date or a YAML 1.1 boolean is written quoted, or some reader would not give a string back",
        ok := (YamlLd.render (j "\"123\"")).startsWith "\"" && (YamlLd.render (j "\"yes\"")).startsWith "\"" && (YamlLd.render (j "\"2018-04-01\"")).startsWith "\"" && !(YamlLd.render (j "\"abc\"")).startsWith "\"" },
      { name := "CONTROL an unquoted 123 read back is a number, not the string", ok := (y "123\n").toOption == some (j "123") && (y "123\n").toOption != some (j "\"123\"") } ] ++
    fileCheck "INVARIANT every file given is a YAML-LD document that reads (a JSON object with an @context)" (fun v => (v.getObjVal? "@context").isOk) ++
    fileCheck "INVARIANT every file given, written and read back, is itself" roundTrips ++
    fileCheck "INVARIANT every file given, written twice, gives the same text" (fun v => YamlLd.render v == (match y (YamlLd.render v) with | .ok w => YamlLd.render w | .error _ => "")) ++
    fileCheck "CONTROL a file written with @context unquoted is refused: @ cannot start a plain scalar" (fun v => (y ((YamlLd.render v).replace "\"@context\"" "@context")).toOption.isNone)
  for ch in checks do IO.println s!"  [{if ch.ok then "ok  " else "FAIL"}] {ch.name}"
  -- the encoding: a file that is not UTF-8 is refused when read, one that is, is read
  let tmp := System.FilePath.mk "yamlld-witness.tmp.yamlld"
  IO.FS.writeBinFile tmp "a: \u00e9\n".toUTF8
  let good ← YamlLd.readFile tmp.toString
  IO.FS.writeBinFile tmp (ByteArray.mk #[0x61, 0x3a, 0x20, 0xff, 0xfe, 0x0a])
  let bad ← YamlLd.readText tmp.toString
  IO.FS.removeFile tmp
  let encOk := (match good with | .ok v => v == j "{\"a\":\"\u00e9\"}" | .error _ => false) && (match bad with | .error _ => true | .ok _ => false)
  IO.println s!"  [{if encOk then "ok  " else "FAIL"}] CONTROL a file that is not UTF-8 is not read (invalid-encoding), and the same file in UTF-8 is"
  let badN := checks.filter (!·.ok) |>.length
  let total := checks.length + 1
  if badN == 0 && encOk then
    IO.println s!"OK: yamlld, {total} checks hold"
    pure 0
  else
    IO.println s!"FAIL: {badN + (if encOk then 0 else 1)} of {total} checks failed"
    pure 1
