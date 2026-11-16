/-! Finds the `<script>` elements and the `<base href>` of an HTML document.

This is for the test runner, not for the YAML-LD library: YAML-LD does not read HTML. It follows the
HTML tokenizer's rules for the cases the W3C tests use: comments, quoted and bare attribute values,
raw text in `script`, `style`, `textarea` and `title`. It does not build a tree. -/

namespace HtmlScripts

structure Script where
  id : Option String
  type : String
  text : String
deriving Repr

structure Found where
  base : Option String := none
  scripts : Array Script := #[]
deriving Repr

private def isWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0C'

private def findFrom (cs : Array Char) (pat : String) (i : Nat) : Nat := Id.run do
  let p := pat.toList.toArray
  let mut k := i
  while k + p.size ≤ cs.size do
    let mut ok := true
    for j in [0:p.size] do
      if cs[k + j]!.toLower != p[j]! then ok := false; break
    if ok then return k
    k := k + 1
  return cs.size

/-- Reads the attributes of a start tag from `i` (just after the tag name). Returns the attributes
and the index after the closing `>`. -/
private def readAttrs (cs : Array Char) (i : Nat) : List (String × String) × Nat := Id.run do
  let mut k := i
  let mut out : List (String × String) := []
  while k < cs.size do
    while k < cs.size && (isWs cs[k]! || cs[k]! == '/') do k := k + 1
    if k >= cs.size then break
    if cs[k]! == '>' then return (out.reverse, k + 1)
    let mut name := ""
    while k < cs.size && !isWs cs[k]! && cs[k]! != '=' && cs[k]! != '>' && cs[k]! != '/' do
      name := name.push cs[k]!.toLower; k := k + 1
    while k < cs.size && isWs cs[k]! do k := k + 1
    let mut val := ""
    if k < cs.size && cs[k]! == '=' then
      k := k + 1
      while k < cs.size && isWs cs[k]! do k := k + 1
      if k < cs.size && (cs[k]! == '"' || cs[k]! == '\'') then
        let q := cs[k]!
        k := k + 1
        while k < cs.size && cs[k]! != q do val := val.push cs[k]!; k := k + 1
        k := k + 1
      else
        while k < cs.size && !isWs cs[k]! && cs[k]! != '>' do val := val.push cs[k]!; k := k + 1
    if name != "" then out := (name, val) :: out
  return (out.reverse, k)

private def attr (as : List (String × String)) (n : String) : Option String :=
  (as.find? (·.1 == n)).map (·.2)

/-- Replaces the character references that can appear in a `href` or `id`. -/
private def decodeRefs (s : String) : String :=
  ((s.replace "&amp;" "&").replace "&quot;" "\"").replace "&#39;" "'"

def extract (html : String) : Found := Id.run do
  let cs := html.toList.toArray
  let mut i := 0
  let mut res : Found := {}
  while i < cs.size do
    if cs[i]! != '<' then i := i + 1; continue
    if i + 3 < cs.size && cs[i+1]! == '!' && cs[i+2]! == '-' && cs[i+3]! == '-' then
      let e := findFrom cs "-->" (i + 4)
      i := e + 3; continue
    if i + 1 < cs.size && (cs[i+1]! == '!' || cs[i+1]! == '?' || cs[i+1]! == '/') then
      while i < cs.size && cs[i]! != '>' do i := i + 1
      i := i + 1; continue
    -- a start tag
    let mut k := i + 1
    let mut name := ""
    while k < cs.size && !isWs cs[k]! && cs[k]! != '>' && cs[k]! != '/' do
      name := name.push cs[k]!.toLower; k := k + 1
    if name == "" then i := i + 1; continue
    let (as, after) := readAttrs cs k
    i := after
    if name == "base" && res.base.isNone then
      res := { res with base := (attr as "href").map decodeRefs }
    else if name == "script" then
      let e := findFrom cs "</script" i
      let text := String.ofList (cs.extract i e).toList
      let sc : Script := { id := (attr as "id").map decodeRefs, type := (attr as "type").getD "", text := text }
      res := { res with scripts := res.scripts.push sc }
      i := e
      while i < cs.size && cs[i]! != '>' do i := i + 1
      i := i + 1
    else if name == "style" || name == "textarea" || name == "title" then
      let e := findFrom cs ("</" ++ name) i
      i := e
      while i < cs.size && cs[i]! != '>' do i := i + 1
      i := i + 1
  return res

/-- True for a script whose type is `application/ld+json` or `application/ld+yaml`, with or without
parameters. -/
def isLd (s : Script) : Bool :=
  let t := (s.type.trimAscii.toString.splitOn ";").head!.trimAscii.toString.toLower
  t == "application/ld+json" || t == "application/ld+yaml"

end HtmlScripts
