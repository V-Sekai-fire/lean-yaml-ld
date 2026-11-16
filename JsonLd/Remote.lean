import Lean.Data.Json
import JsonLd.Iri

/-! The default document loader of the JSON-LD API (section 9.2): redirects, the `Link` header and
the content type decide which document is read and which context goes with it.

This module holds the decisions only. It takes the transport as a function, so any HTTP/1.1 client
fits, and it does not read the body: the caller parses JSON, YAML or HTML. -/

namespace JsonLd.Remote

/-- What a transport answers for one request. -/
structure Response where
  status : Nat
  contentType : String := ""
  /-- Every `Link` header value, one entry per header. -/
  links : Array String := #[]
  location : Option String := none
  body : String := ""

/-- A loaded document, before its body is parsed. -/
structure RemoteDocument where
  documentUrl : String
  contentType : String
  body : String
  contextUrl : Option String := none

/-- One member of a `Link` header: its target and its parameters, names lowercased. -/
structure Link where
  target : String
  params : List (String × String)

private def unquote (s : String) : String :=
  let t := s.trimAscii.toString
  if t.length ≥ 2 && t.startsWith "\"" && t.endsWith "\"" then (t.drop 1).dropEnd 1 |>.toString else t

/-- Reads one `Link` header value (RFC 8288): `<target>; rel="x"; type="y"`, separated by commas. -/
def parseLinks (value : String) : List Link := Id.run do
  let mut out : List Link := []
  let mut rest := value.trimAscii.toString
  while rest.startsWith "<" do
    let parts := (rest.drop 1).toString.splitOn ">"
    let target := parts.head!
    let after : String := ">".intercalate parts.tail!
    -- parameters run to the next comma that is followed by `<`
    let mut paramText := after
    let mut tail := ""
    match after.splitOn ", <" with
    | [] => pure ()
    | [only] => paramText := only
    | h :: t => paramText := h; tail := "<" ++ ", <".intercalate t
    let params := (paramText.splitOn ";").filterMap fun p =>
      match p.splitOn "=" with
      | k :: v :: more => some (k.trimAscii.toString.toLower, unquote ("=".intercalate (v :: more)))
      | _ => none
    out := out ++ [({ target := target, params := params } : Link)]
    rest := tail.trimAscii.toString
  return out

def param (l : Link) (k : String) : Option String := (l.params.find? (·.1 == k)).map (·.2)

/-- The media type without parameters, lowercased. -/
def mediaType (ct : String) : String := ((ct.splitOn ";").head!).trimAscii.toString.toLower

def isJsonLd (ct : String) : Bool := mediaType ct == "application/ld+json"
def isJson (ct : String) : Bool := let m := mediaType ct; m == "application/json" || m.endsWith "+json"
def isHtml (ct : String) : Bool := let m := mediaType ct; m == "text/html" || m == "application/xhtml+xml"

/-- Loads `url` through `fetch`. Errors are JSON-LD error codes. -/
def load (fetch : String → IO (Except String Response)) (url : String) : IO (Except String RemoteDocument) := do
  let mut current := url
  let mut documentUrl := url
  for _ in [0:20] do
    match ← fetch current with
    | .error _ => return .error "loading document failed"
    | .ok r =>
      if r.status ≥ 300 && r.status < 400 then
        let some loc := r.location | return .error "loading document failed"
        current := resolveIri current loc
        -- The API text excludes 303 from the document URL, but test #t0006 of the W3C suite expects the
        -- target's URL as base after a 303, so every redirect moves it.
        documentUrl := current
        continue
      if r.status < 200 || r.status ≥ 300 then return .error "loading document failed"
      let links := r.links.toList.flatMap parseLinks
      let alt := links.find? fun l => param l "rel" == some "alternate" && param l "type" == some "application/ld+json"
      if !isJson r.contentType && !isJsonLd r.contentType then
        if let some a := alt then
          current := resolveIri current a.target
          documentUrl := current
          continue
      if isJson r.contentType && !isJsonLd r.contentType then
        let ctxLinks := links.filter fun l => param l "rel" == some "http://www.w3.org/ns/json-ld#context"
        match ctxLinks with
        | [] => return .ok { documentUrl, contentType := r.contentType, body := r.body }
        | [l] => return .ok { documentUrl, contentType := r.contentType, body := r.body,
                              contextUrl := some (resolveIri current l.target) }
        | _ => return .error "multiple context link headers"
      if isJsonLd r.contentType || isHtml r.contentType then
        return .ok { documentUrl, contentType := r.contentType, body := r.body }
      return .error "loading document failed"
  return .error "loading document failed"

end JsonLd.Remote
