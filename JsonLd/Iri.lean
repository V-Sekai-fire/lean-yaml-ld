import Lean.Data.Json

/-! IRI handling for the JSON-LD processor: the parts of RFC 3986 that JSON-LD asks for (parse, resolve, and the tests for an absolute IRI,
a blank node identifier and a keyword). -/

namespace JsonLd
open Lean

def ofChars (cs : List Char) : String := cs.foldl String.push ""

/-- The text before the first `c`, and the text after it. -/
def splitFirst (s : String) (c : Char) : Option (String × String) :=
  let cs := s.toList
  let pre := cs.takeWhile (· != c)
  if pre.length == cs.length then none else some (ofChars pre, ofChars (cs.drop (pre.length + 1)))

def startsWithS (s p : String) : Bool := s.startsWith p
def endsWithS (s p : String) : Bool := s.endsWith p

def keywords : List String :=
  ["@base", "@container", "@context", "@direction", "@graph", "@id", "@import", "@included", "@index", "@json", "@language",
   "@list", "@nest", "@none", "@prefix", "@propagate", "@protected", "@reverse", "@set", "@type", "@value", "@version", "@vocab"]

def isKeyword (s : String) : Bool := keywords.contains s

/-- `@` followed by letters only: it looks like a keyword, whether or not it is one. -/
def keywordLike (s : String) : Bool :=
  match s.toList with
  | '@' :: rest@(_ :: _) => rest.all Char.isAlpha
  | _ => false

def isSchemeChar (c : Char) : Bool := c.isAlphanum || c == '+' || c == '-' || c == '.'

/-- The scheme of an IRI, when it starts with one. -/
def schemeOf (s : String) : Option String :=
  match s.toList with
  | c :: rest =>
    if c.isAlpha then
      let body := rest.takeWhile isSchemeChar
      if (rest.drop body.length).head? == some ':' then some (ofChars (c :: body)) else none
    else none
  | [] => none

def isAbsoluteIri (s : String) : Bool := (schemeOf s).isSome && !s.toList.any Char.isWhitespace

def isBlankNode (s : String) : Bool := s.startsWith "_:"

structure Parts where
  scheme : Option String := none
  authority : Option String := none
  path : String := ""
  query : Option String := none
  fragment : Option String := none

def parseIri (s : String) : Parts :=
  let (rest, frag) := match splitFirst s '#' with | some (a, b) => (a, some b) | none => (s, none)
  let (rest, query) := match splitFirst rest '?' with | some (a, b) => (a, some b) | none => (rest, none)
  let (scheme, rest) := match schemeOf rest with
    | some sc => (some sc, (rest.drop (sc.length + 1)).toString)
    | none => (none, rest)
  if rest.startsWith "//" then
    let r := (rest.drop 2).toString.toList
    let auth := r.takeWhile (· != '/')
    { scheme, authority := some (ofChars auth), path := ofChars (r.drop auth.length), query, fragment := frag }
  else { scheme, authority := none, path := rest, query, fragment := frag }

def composeIri (p : Parts) : String :=
  (match p.scheme with | some s => s ++ ":" | none => "") ++
  (match p.authority with | some a => "//" ++ a | none => "") ++ p.path ++
  (match p.query with | some q => "?" ++ q | none => "") ++
  (match p.fragment with | some f => "#" ++ f | none => "")

/-- RFC 3986 5.2.4. -/
def removeDotSegments (path : String) : String := Id.run do
  let mut input := path
  let mut out : List String := []   -- reversed segments, each with its leading "/"
  let mut fuel := path.length * 2 + 8
  while !input.isEmpty && fuel > 0 do
    fuel := fuel - 1
    if input.startsWith "../" then input := (input.drop 3).toString
    else if input.startsWith "./" then input := (input.drop 2).toString
    else if input.startsWith "/./" then input := "/" ++ (input.drop 3).toString
    else if input == "/." then input := "/"
    else if input.startsWith "/../" then
      input := "/" ++ (input.drop 4).toString
      out := out.drop 1
    else if input == "/.." then
      input := "/"
      out := out.drop 1
    else if input == "." || input == ".." then input := ""
    else
      let cs := input.toList
      let first := cs.head!
      let seg := first :: (cs.tail!.takeWhile (· != '/'))
      out := ofChars seg :: out
      input := ofChars (cs.drop seg.length)
  return String.join out.reverse

/-- RFC 3986 5.2.2, strict. -/
def resolveIri (base ref : String) : String :=
  let r := parseIri ref
  let b := parseIri base
  if r.scheme.isSome then composeIri { r with path := removeDotSegments r.path }
  else if r.authority.isSome then composeIri { r with scheme := b.scheme, path := removeDotSegments r.path }
  else if r.path.isEmpty then
    composeIri { b with query := (if r.query.isSome then r.query else b.query), fragment := r.fragment }
  else
    let merged :=
      if r.path.startsWith "/" then r.path
      else if b.authority.isSome && b.path.isEmpty then "/" ++ r.path
      else
        let bp := b.path.toList
        let keep := (bp.reverse.dropWhile (· != '/')).reverse
        ofChars keep ++ r.path
    composeIri { b with path := removeDotSegments merged, query := r.query, fragment := r.fragment }

end JsonLd
