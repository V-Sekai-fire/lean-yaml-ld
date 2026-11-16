import Lean.Data.Json

/-! A YAML-LD 1.0 reader and writer (https://www.w3.org/TR/yaml-ld/). It turns a YAML-LD stream into `Lean.Json` and back.

What the specification asks, and where it is met:
- 4.1.1: a stream is UTF-8. A file that is not is refused when it is read (`readText`).
- 4.1.3 and 4.4.1: a stream holds one or more documents. `parseAll` is `extractAllScripts` true, `parse` is false.
- 4.2.1 and 4.3: anchors are copied where aliased and their names are dropped. An alias of an anchor that is not yet complete
  would be a cycle, and is refused.
- 4.3.1: scalars resolve by the YAML Core Schema. `no`, `yes` and `on` are strings. `2018-04-01` is a string. `.inf` and `.nan` are refused.
- 4.4.2: every mapping key is a string, or `mapping-key-error`. A mapping used as a key is refused the same way. A key may be
  explicit (`? `), and may carry an anchor, a tag or be an alias, so long as it comes out a string.
- Comments are whitespace. A tag of the Core Schema forces its type (a `%TAG` handle or a verbatim `!<...>` that names one is the same tag); a tag of another namespace adds no meaning and is ignored (4.3.1).

The reader takes block and flow collections, plain, single- and double-quoted scalars, literal and folded block scalars, anchors,
aliases, comments, `%YAML` and document markers. JSON is YAML, so a JSON-LD file reads through it too.
Not taken, and refused with an error code: tabs as indentation. -/

namespace YamlLd
open Lean

structure St where
  s : Array Char
  i : Nat := 0
  anchors : List (String × Json) := []
  /-- `%TAG` handles of the current document, as (handle, prefix). -/
  tags : List (String × String) := []

abbrev M := StateT St (Except String)

instance : Inhabited (M α) := ⟨fun _ => .error "unreachable"⟩

def lineOf (st : St) : Nat := (st.s.extract 0 st.i).foldl (fun n c => if c == '\n' then n + 1 else n) 1

/-- Fail with the code of the specification. Text that is not well-formed YAML is `loading-document-failed` (4.1.3). -/
def fail (code msg : String) : M α := do
  let st ← get
  if code == "syntax-error" then throw s!"loading-document-failed: syntax: {msg} (line {lineOf st})"
  else throw s!"{code}: {msg} (line {lineOf st})"

def peekAt (k : Nat) : M (Option Char) := do
  let st ← get
  pure st.s[st.i + k]?

def peek : M (Option Char) := peekAt 0

def adv (k : Nat := 1) : M Unit := modify fun st => { st with i := st.i + k }

def isWs (c : Char) : Bool := c == ' ' || c == '\t'

def isSep (o : Option Char) : Bool :=
  match o with
  | none => true
  | some c => isWs c || c == '\n'

def isFlowInd (c : Char) : Bool := c == ',' || c == '[' || c == ']' || c == '{' || c == '}'

def isFlowIndO (o : Option Char) : Bool :=
  match o with
  | some c => isFlowInd c
  | none => false

def trimEndWs (s : String) : String :=
  ((s.toList.reverse.dropWhile isWs).reverse).foldl String.push ""

def newlines (n : Nat) : String := "".pushn '\n' n

/-- The column of the position: how far it is from the start of its line. -/
def col : M Nat := do
  let st ← get
  let mut j := st.i
  while j > 0 && st.s[j - 1]! != '\n' do
    j := j - 1
  pure (st.i - j)

/-- Spaces, tabs and a comment up to the end of the line. A `#` starts a comment only after whitespace or at the start of a line. -/
def skipInline : M Unit := do
  repeat
    match ← peek with
    | some c =>
      if isWs c then adv else break
    | none => break
  match ← peek with
  | some '#' =>
    let st ← get
    if st.i == 0 || isWs st.s[st.i - 1]! || st.s[st.i - 1]! == '\n' then
      repeat
        match ← peek with
        | some c =>
          if c == '\n' then break else adv
        | none => break
  | _ => pure ()

/-- Whitespace, comments and line breaks, up to the next content or the end. A tab may separate but never indent. -/
partial def skipBlank : M Unit := do
  skipInline
  match ← peek with
  | some '\n' =>
    adv
    repeat
      if (← peek) == some ' ' then adv else break
    if (← peek) == some '\t' then
      repeat
        match ← peek with
        | some c =>
          if isWs c then adv else break
        | none => break
      match ← peek with
      | none | some '\n' | some '#' => pure ()
      | _ => fail "syntax-error" "a tab is used as indentation"
    skipBlank
  | _ => pure ()

def atDocMarker : M Bool := do
  if (← col) != 0 then return false
  let a ← peekAt 0
  let b ← peekAt 1
  let c ← peekAt 2
  let d ← peekAt 3
  pure (((a == some '-' && b == some '-' && c == some '-') || (a == some '.' && b == some '.' && c == some '.')) && isSep d)

def readName : M String := do
  let mut r := ""
  repeat
    match ← peek with
    | some c =>
      if isWs c || c == '\n' || isFlowInd c then break
      else
        adv
        r := r.push c
    | none => break
  pure r

/-- The tag URI of a handle: one a `%TAG` gave, else the default of `!` and `!!` (YAML 1.2, 6.8.2.2). -/
def handlePrefix (h : String) : M (Option String) := do
  match (← get).tags.lookup h with
  | some p => pure (some p)
  | none => pure (if h == "!!" then some "tag:yaml.org,2002:" else if h == "!" then some "!" else none)

/-- A tag as written (`!!str`, `!e!x`, `!<uri>`), as its Core Schema short form `!!x` when it is in the yaml.org namespace,
else as its full URI. `!` alone stays `!`, the non-specific tag. -/
def readTag : M String := do
  let canon (uri : String) : String :=
    if uri.startsWith "tag:yaml.org,2002:" then "!!" ++ (uri.drop 18).toString else uri
  if (← peekAt 1) == some '<' then
    adv 2
    let mut uri := ""
    repeat
      match ← peek with
      | some '>' =>
        adv
        break
      | some c =>
        if c == '\n' then fail "syntax-error" "a verbatim tag is not closed"
        adv
        uri := uri.push c
      | none => fail "syntax-error" "a verbatim tag is not closed"
    if uri.isEmpty || uri == "!" then fail "syntax-error" "a verbatim tag is empty"
    return canon uri
  let raw ← readName
  if raw == "!" then return "!"
  let body := (raw.drop 1).toString
  match body.splitOn "!" with
  | [_] =>
    match ← handlePrefix "!" with
    | some p => pure (canon (p ++ body))
    | none => fail "syntax-error" "no primary tag handle"
  | name :: rest@(_ :: _) =>
    let h := "!" ++ name ++ "!"
    match ← handlePrefix h with
    | some p => pure (canon (p ++ "!".intercalate rest))
    | none => fail "syntax-error" s!"the tag handle {h} is not declared by a %TAG directive"
  | [] => fail "syntax-error" "a tag is empty"

/-- Anchors (`&name`) and tags (`!!str`) before a node. -/
def parseProps : M (Option String × Option String) := do
  let mut anchor : Option String := none
  let mut tag : Option String := none
  repeat
    match ← peek with
    | some '&' =>
      adv
      anchor := some (← readName)
    | some '!' =>
      tag := some (← readTag)
    | _ => break
    skipInline
  pure (anchor, tag)

/-! ## Scalars: the Core Schema -/

def isHex (c : Char) : Bool := c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

def hexVal (c : Char) : Nat :=
  if c.isDigit then c.toNat - 48 else if c ≥ 'a' then c.toNat - 87 else c.toNat - 55

def digitsVal (ds : List Char) : Nat := ds.foldl (fun a c => a * 10 + (c.toNat - 48)) 0

/-- An integer or float of the Core Schema; the exact digits are kept, so `100.0` and `1.50` keep their shape. -/
def parseNumber (s : String) : Option Json :=
  match s.toList with
  | '0' :: 'x' :: ds@(_ :: _) =>
    if ds.all isHex then some (Json.num ⟨(ds.foldl (fun a c => a * 16 + hexVal c) 0 : Nat), 0⟩) else none
  | '0' :: 'o' :: ds@(_ :: _) =>
    if ds.all (fun c => '0' ≤ c && c ≤ '7') then some (Json.num ⟨(ds.foldl (fun a c => a * 8 + (c.toNat - 48)) 0 : Nat), 0⟩)
    else none
  | cs =>
    let (neg, body) := match cs with
      | '-' :: r => (true, r)
      | '+' :: r => (false, r)
      | r => (false, r)
    let ip := body.takeWhile Char.isDigit
    let rest := body.dropWhile Char.isDigit
    let hasDot := rest.head? == some '.'
    let afterDot := if hasDot then rest.drop 1 else rest
    let fd := if hasDot then afterDot.takeWhile Char.isDigit else []
    let rest2 := if hasDot then afterDot.dropWhile Char.isDigit else rest
    let sign (m : Nat) : Int := if neg then -(m : Int) else (m : Int)
    if rest.isEmpty && !ip.isEmpty then some (Json.num ⟨sign (digitsVal ip), 0⟩)
    else if ip.isEmpty && fd.isEmpty then none
    else
      let exp : Option Int :=
        match rest2 with
        | [] => some 0
        | e :: r =>
          if e == 'e' || e == 'E' then
            let (eneg, ds) := match r with
              | '-' :: q => (true, q)
              | '+' :: q => (false, q)
              | q => (false, q)
            if !ds.isEmpty && ds.all Char.isDigit then some (if eneg then -(digitsVal ds : Int) else (digitsVal ds : Int)) else none
          else none
      match exp with
      | none => none
      | some ex =>
        let m := sign (digitsVal (ip ++ fd))
        let fr := fd.length
        if ex ≥ (fr : Int) then some (Json.num ⟨m * (10 : Int) ^ (ex - fr).toNat, 0⟩)
        else some (Json.num ⟨m, (fr - ex).toNat⟩)

/-- A plain scalar under the Core Schema. `.inf` and `.nan` have no JSON form and are refused (4.3.1). -/
def resolvePlain (s : String) : Except String Json :=
  if s == "" || s == "~" || s == "null" || s == "Null" || s == "NULL" then .ok Json.null
  else if s == "true" || s == "True" || s == "TRUE" then .ok (Json.bool true)
  else if s == "false" || s == "False" || s == "FALSE" then .ok (Json.bool false)
  else if [".inf", ".Inf", ".INF", "+.inf", "+.Inf", "+.INF", "-.inf", "-.Inf", "-.INF", ".nan", ".NaN", ".NAN"].contains s then
    .error s!"loading-document-failed: {s} has no JSON form"
  else match parseNumber s with
    | some j => .ok j
    | none => .ok (Json.str s)

def isStr : Json → Bool
  | .str _ => true
  | _ => false

def isNull : Json → Bool
  | .null => true
  | _ => false

def isBool : Json → Bool
  | .bool _ => true
  | _ => false

def isNum : Json → Bool
  | .num _ => true
  | _ => false

def isInt : Json → Bool
  | .num n => n.exponent == 0
  | _ => false

/-- A scalar read from the text, as the Core Schema or its tag says. A tag outside the Core Schema is a `profile-error`. -/
def resolveScalar (tag : Option String) (text : String) (plain : Bool) : M Json := do
  let viaCore : M Json := match resolvePlain text with
    | .ok j => pure j
    | .error m => throw m
  match tag with
  | none => if plain then viaCore else pure (Json.str text)
  | some "!" | some "!!str" => pure (Json.str text)
  | some t =>
    let j ← viaCore
    let ok := (t == "!!null" && isNull j) || (t == "!!bool" && isBool j) || (t == "!!int" && isInt j) ||
      (t == "!!float" && isNum j)
    if ["!!null", "!!bool", "!!int", "!!float"].contains t then
      if ok then pure j else fail "loading-document-failed" s!"{text} is not a {t}"
    else if t.startsWith "!!" then fail "profile-error" s!"the tag {t} is not in the Core Schema"
    else if plain then viaCore else pure (Json.str text)   -- a tag of another namespace adds no meaning (4.3.1): read as untagged

def checkCollectionTag (tag : Option String) (j : Json) : M Unit :=
  match tag with
  | none | some "!" => pure ()
  | some "!!map" => (match j with | .obj _ => pure () | _ => fail "loading-document-failed" "!!map on a non-mapping")
  | some "!!seq" => (match j with | .arr _ => pure () | _ => fail "loading-document-failed" "!!seq on a non-sequence")
  | some t => if t.startsWith "!!" then fail "profile-error" s!"the tag {t} is not in the Core Schema" else pure ()

def register (anchor : Option String) (j : Json) : M Unit :=
  match anchor with
  | some a => modify fun st => { st with anchors := (a, j) :: st.anchors }
  | none => pure ()

def readAlias : M Json := do
  adv
  let name ← readName
  let st ← get
  match st.anchors.lookup name with
  | some j => pure j
  | none => fail "loading-document-failed" s!"the alias *{name} names no anchor that is complete (an anchor cannot hold itself)"

/-! ## Quoted scalars -/

def escChar : Char → Option Char
  | '0' => some '\x00'
  | 'a' => some '\x07'
  | 'b' => some '\x08'
  | 't' => some '\t'
  | '\t' => some '\t'
  | 'n' => some '\n'
  | 'v' => some '\x0b'
  | 'f' => some '\x0c'
  | 'r' => some '\r'
  | 'e' => some '\x1b'
  | ' ' => some ' '
  | '"' => some '"'
  | '/' => some '/'
  | '\\' => some '\\'
  | 'N' => some '\u0085'
  | '_' => some '\u00a0'
  | 'L' => some '\u2028'
  | 'P' => some '\u2029'
  | _ => none

def skipLeadingWs : M Unit := do
  repeat
    match ← peek with
    | some c =>
      if isWs c then adv else break
    | none => break

/-- A quoted scalar. A line break inside folds to one space, and a run of blank lines to that many breaks. -/
def readQuoted (dq : Bool) : M String := do
  adv
  let q := if dq then '"' else '\''
  let mut acc := ""
  let mut pend := ""
  repeat
    match ← peek with
    | none => fail "syntax-error" "a quoted scalar is not closed"
    | some c =>
      if c == q && (dq || (← peekAt 1) != some '\'') then
        acc := acc ++ pend
        pend := ""
        adv
        break
      else if !dq && c == '\'' then
        adv 2
        acc := acc ++ pend ++ "'"
        pend := ""
      else if dq && c == '\\' then
        acc := acc ++ pend
        pend := ""
        adv
        let e ← peek
        match e with
        | some '\n' =>
          adv
          skipLeadingWs
        | some x =>
          if x == 'x' || x == 'u' || x == 'U' then
            let k := if x == 'x' then 2 else if x == 'u' then 4 else 8
            adv
            let mut v := 0
            for _ in [0:k] do
              match ← peek with
              | some h =>
                if isHex h then
                  v := v * 16 + hexVal h
                  adv
                else fail "syntax-error" "bad hexadecimal escape"
              | none => fail "syntax-error" "bad hexadecimal escape"
            if Nat.isValidChar v then acc := acc.push (Char.ofNat v)
            else fail "syntax-error" "an escape is not a character"
          else
            match escChar x with
            | some r =>
              adv
              acc := acc.push r
            | none => fail "syntax-error" s!"unknown escape \\{x}"
        | none => fail "syntax-error" "a quoted scalar is not closed"
      else if c == '\n' then
        pend := ""
        let mut blanks := 0
        adv
        skipLeadingWs
        while (← peek) == some '\n' do
          blanks := blanks + 1
          adv
          skipLeadingWs
        acc := acc ++ (if blanks == 0 then " " else newlines blanks)
      else if isWs c then
        pend := pend.push c
        adv
      else
        acc := acc ++ pend
        pend := ""
        acc := acc.push c
        adv
  pure acc

/-! ## Plain scalars -/

/-- One line of a plain scalar: up to `: `, ` #`, a flow indicator when in flow, or the end of the line. -/
def plainLine (flow : Bool) : M String := do
  let mut r := ""
  repeat
    match ← peek with
    | none => break
    | some '\n' => break
    | some c =>
      let nxt ← peekAt 1
      let st ← get
      if c == ':' && (isSep nxt || (flow && isFlowIndO nxt)) then break
      else if c == '#' && st.i > 0 && isWs st.s[st.i - 1]! then break
      else if flow && isFlowInd c then break
      else
        adv
        r := r.push c
  pure (trimEndWs r)

/-- If a plain scalar goes on to a next line: step to its content and say how many blank lines lay between. Otherwise stay put. -/
def nextPlainLine (n : Int) (flow : Bool) : M (Option Nat) := do
  let save ← get
  let mut blanks := 0
  if (← peek) != some '\n' then return none
  repeat
    match ← peek with
    | some '\n' =>
      adv
      skipLeadingWs
      if (← peek) == some '\n' then blanks := blanks + 1 else break
    | _ => break
  let c ← col
  let stop : Bool ← match ← peek with
    | none => pure true
    | some '#' => pure true
    | some ch =>
      if flow then pure (isFlowInd ch)
      else if (c : Int) ≤ n then pure true
      else atDocMarker
  if stop then
    set save
    pure none
  else pure (some blanks)

partial def readPlain (n : Int) (flow : Bool) : M String := do
  match ← peek with
  | some c =>
    if c == '%' || c == '@' || c == '`' then fail "syntax-error" s!"{c} cannot start a plain scalar"
    else if flow && isFlowInd c then fail "syntax-error" s!"unexpected {c}"
  | none => pure ()
  let mut res ← plainLine flow
  repeat
    match ← nextPlainLine n flow with
    | none => break
    | some b =>
      let more ← plainLine flow
      res := res ++ (if b == 0 then " " else newlines b) ++ more
  pure res

/-! ## Block scalars -/

def isMore (l : String) : Bool := l.startsWith " " || l.startsWith "\t"

def fold (ls : List String) : String := Id.run do
  let mut res := ""
  let mut blanks := 0
  let mut seen := false
  let mut prevMore := false
  for l in ls do
    if l == "" then blanks := blanks + 1
    else
      let more := isMore l
      if !seen then res := newlines blanks ++ l
      else
        let sep := if !more && !prevMore then (if blanks == 0 then " " else newlines blanks) else newlines (blanks + 1)
        res := res ++ sep ++ l
      seen := true
      prevMore := more
      blanks := 0
  pure res

/-- `|` and `>` scalars. `n` is the indent of the node that holds it. -/
def readBlockScalar (n : Int) : M String := do
  let folded := (← peek) == some '>'
  adv
  let mut chomp := 'c'
  let mut ind : Nat := 0
  repeat
    match ← peek with
    | some '+' =>
      chomp := 'k'
      adv
    | some '-' =>
      chomp := 's'
      adv
    | some d =>
      if '1' ≤ d && d ≤ '9' then
        ind := d.toNat - 48
        adv
      else break
    | none => break
  skipInline
  match ← peek with
  | none | some '\n' => pure ()
  | _ => fail "syntax-error" "text follows a block scalar header"
  let mut lines : Array String := #[]
  let mut blockInd : Option Nat := if ind > 0 then some (n + ind).toNat else none
  repeat
    match ← peek with
    | some '\n' =>
      let nlPos := (← get).i
      adv
      let mut raw := ""
      repeat
        match ← peek with
        | some c =>
          if c == '\n' then break
          else
            adv
            raw := raw.push c
        | none => break
      let sp := (raw.toList.takeWhile (· == ' ')).length
      let blank := raw.all (· == ' ')
      let isMarker := (raw.startsWith "---" || raw.startsWith "...") && (raw.length == 3 || isWs (raw.toList[3]!))
      let mut stop := isMarker
      if !stop then
        match blockInd with
        | none =>
          if blank then lines := lines.push ""
          else if (sp : Int) > n then
            blockInd := some sp
            lines := lines.push (raw.drop sp).toString
          else stop := true
        | some b =>
          if blank && sp ≤ b then lines := lines.push ""
          else if sp ≥ b then lines := lines.push (raw.drop b).toString
          else stop := true
      if stop then
        modify fun st => { st with i := nlPos }
        break
    | _ => break
  let mut ls := lines.toList
  let mut trailing := 0
  while ls.getLast? == some "" do
    ls := ls.dropLast
    trailing := trailing + 1
  let core := if folded then fold ls else "\n".intercalate ls
  pure (match chomp with
    | 's' => core
    | 'k' => if ls.isEmpty then newlines trailing else core ++ "\n" ++ newlines trailing
    | _ => if ls.isEmpty then "" else core ++ "\n")

/-! ## Collections -/

/-- Is there a `key:` on this line? A quoted, plain or flow key counts. -/
def keyAhead : M Bool := do
  let st ← get
  let s := st.s
  let mut j := st.i
  match s[j]? with
  | none => return false
  | some q =>
    if q == '"' || q == '\'' then
      j := j + 1
      let mut closed := false
      while j < s.size && !closed && s[j]! != '\n' do
        let c := s[j]!
        if q == '"' && c == '\\' then j := j + 2
        else if c == q then
          if q == '\'' && s[j + 1]? == some '\'' then j := j + 2
          else
            closed := true
            j := j + 1
        else j := j + 1
      if !closed then return false
    else if q == '[' || q == '{' then
      let mut depth := 0
      let mut done := false
      while j < s.size && !done && s[j]! != '\n' do
        let c := s[j]!
        if c == '[' || c == '{' then depth := depth + 1
        else if c == ']' || c == '}' then
          depth := depth - 1
          if depth == 0 then done := true
        j := j + 1
      if !done then return false
    else
      while j < s.size && s[j]! != '\n' do
        let c := s[j]!
        if c == ':' && isSep s[j + 1]? then return true
        if c == '#' && j > st.i && isWs s[j - 1]! then return false
        j := j + 1
      return false
  while j < s.size && isWs s[j]! do j := j + 1
  pure (s[j]? == some ':' && isSep s[j + 1]?)

/-- A mapping key, with the anchor and tag it may carry. Whatever it is, it must come out a string (4.4.2). -/
def readKey : M String := do
  let (anchor, tag) ← parseProps
  let j : Json ← match ← peek with
    | some '"' => resolveScalar tag (← readQuoted true) false
    | some '\'' => resolveScalar tag (← readQuoted false) false
    | some '[' | some '{' => fail "mapping-key-error" "a collection is used as a mapping key"
    | some '*' =>
      if anchor.isSome || tag.isSome then fail "syntax-error" "an alias takes no properties"
      else readAlias
    | some c =>
      if c == '%' || c == '@' || c == '`' then fail "syntax-error" s!"{c} cannot start a plain scalar; quote the key"
      else resolveScalar tag (← plainLine false) true
    | none => fail "syntax-error" "a key is missing"
  match j with
  | .str _ =>
    register anchor j
    pure (match j with | .str k => k | _ => "")
  | _ => fail "mapping-key-error" "a mapping key is not a string"

def addKey (kvs : List (String × Json)) (k : String) (v : Json) : M (List (String × Json)) :=
  if kvs.any (·.1 == k) then fail "loading-document-failed" s!"the key {k} is given twice"
  else pure (kvs ++ [(k, v)])

/-- Does an entry of a block mapping start here: `? ` or a `key:`? -/
def entryAhead : M Bool := do
  if (← peek) == some '?' && isSep (← peekAt 1) then return true
  keyAhead

mutual

/-- A node in block context. `n` is the indent of the collection that holds it. -/
partial def blockNode (n : Int) (seqAtN sameLineMapOk : Bool) : M Json := do
  skipInline
  let save0 ← get
  let (a1, t1) ← parseProps
  let mut sameLine := true
  let mut save := save0
  let mut anchor := a1
  let mut tag := t1
  let mut lineProps := a1.isSome || t1.isSome
  match ← peek with
  | none | some '\n' =>
    skipBlank
    sameLine := false
    -- properties may also start the next line, and are those of the key if a key follows them
    save ← get
    let (a2, t2) ← parseProps
    anchor := a2.orElse fun _ => a1
    tag := t2.orElse fun _ => t1
    lineProps := a2.isSome || t2.isSome
    -- properties alone on a line belong to the node that starts on the next one
    if lineProps && ((← peek).isNone || (← peek) == some '\n') then
      skipBlank
      lineProps := false
  | _ => pure ()
  let c ← col
  let atEnd := (← peek).isNone || (← atDocMarker)
  let seqHere := (← peek) == some '-' && isSep (← peekAt 1)
  if atEnd || (!sameLine && (c : Int) ≤ n && !(seqAtN && (c : Int) == n && seqHere)) then
    let j ← resolveScalar tag "" true
    register anchor j
    return j
  let ch := ((← peek).getD ' ')
  if lineProps && ch != '|' && ch != '>' && !seqHere && !(ch == '?' && isSep (← peekAt 1)) && (← keyAhead) then
    -- the properties on this line belong to the first key, not to the mapping; those of the line above are the mapping's
    if sameLine && !sameLineMapOk then fail "syntax-error" "a block mapping starts on the line of its key"
    set save
    skipInline
    let r ← parseMap (← col)
    unless sameLine do
      checkCollectionTag t1 r
      register a1 r
    return r
  let j ← if ch == '|' || ch == '>' then
      resolveScalar tag (← readBlockScalar n) false
    else if ch == '-' && seqHere then
      if sameLine && !sameLineMapOk then fail "syntax-error" "a block sequence starts on the line of its key"
      else
        let r ← parseSeq c
        checkCollectionTag tag r
        pure r
    else if ch == '?' && isSep (← peekAt 1) then
      if sameLine && !sameLineMapOk then fail "syntax-error" "a block mapping starts on the line of its key"
      else if sameLine && (anchor.isSome || tag.isSome) then fail "syntax-error" "properties before ? belong on the line above"
      else
        let r ← parseMap c
        checkCollectionTag tag r
        pure r
    else if (← keyAhead) then
      if sameLine && !sameLineMapOk then fail "syntax-error" "a block mapping starts on the line of its key"
      else
        let r ← parseMap c
        checkCollectionTag tag r
        pure r
    else if ch == '"' then resolveScalar tag (← readQuoted true) false
    else if ch == '\'' then resolveScalar tag (← readQuoted false) false
    else if ch == '[' || ch == '{' then
      let r ← flowNode
      pure r
    else if ch == '*' then
      readAlias
    else resolveScalar tag (← readPlain n false) true
  register anchor j
  pure j

partial def parseSeq (c : Nat) : M Json := do
  let mut items : Array Json := #[]
  repeat
    adv
    let v ← blockNode (c : Int) false true
    items := items.push v
    skipBlank
    if (← peek).isNone || (← atDocMarker) then break
    let c2 ← col
    if c2 < c then break
    if c2 > c then fail "syntax-error" "bad indentation of a sequence entry"
    unless (← peek) == some '-' && isSep (← peekAt 1) do break
  pure (Json.arr items)

/-- `? key` and an optional `: value` on a line of its own at the indent of the mapping. The key node must be a string. -/
partial def explicitEntry (c : Nat) : M (String × Json) := do
  adv
  let k ← blockNode (c : Int) false true
  let key ← match k with
    | .str s => pure s
    | _ => fail "mapping-key-error" "a mapping key is not a string"
  skipBlank
  if (← col) == c && (← peek) == some ':' && isSep (← peekAt 1) then
    adv
    let v ← blockNode (c : Int) true true
    pure (key, v)
  else pure (key, Json.null)

partial def parseMap (c : Nat) : M Json := do
  let mut kvs : List (String × Json) := []
  repeat
    let (key, v) ← if (← peek) == some '?' && isSep (← peekAt 1) then explicitEntry c
      else do
        let key ← readKey
        skipInline
        unless (← peek) == some ':' do fail "syntax-error" "a ':' is missing after a key"
        adv
        let v ← blockNode (c : Int) true false
        pure (key, v)
    kvs ← addKey kvs key v
    skipBlank
    if (← peek).isNone || (← atDocMarker) then break
    let c2 ← col
    if c2 < c then break
    if c2 > c then fail "syntax-error" "bad indentation of a mapping entry"
    unless (← entryAhead) do fail "syntax-error" "a mapping key is expected"
  pure (Json.mkObj kvs)

/-- A node in flow context (`[...]`, `{...}`, or a scalar inside them). -/
partial def flowNode : M Json := do
  skipBlank
  let (anchor, tag) ← parseProps
  skipBlank
  let j ← match ← peek with
    | some '[' =>
      let r ← flowSeq
      checkCollectionTag tag r
      pure r
    | some '{' =>
      let r ← flowMap
      checkCollectionTag tag r
      pure r
    | some '"' => resolveScalar tag (← readQuoted true) false
    | some '\'' => resolveScalar tag (← readQuoted false) false
    | some '*' => readAlias
    | none => fail "syntax-error" "a flow collection is not closed"
    | _ => resolveScalar tag (← readPlain (-1) true) true
  register anchor j
  pure j

partial def flowValueAfterColon : M Json := do
  adv
  skipBlank
  match ← peek with
  | some ',' | some ']' | some '}' => pure Json.null
  | _ => flowNode

partial def flowSeq : M Json := do
  adv
  let mut items : Array Json := #[]
  repeat
    skipBlank
    match ← peek with
    | some ']' =>
      adv
      break
    | none => fail "syntax-error" "a flow sequence is not closed"
    | _ => pure ()
    let explicit := (← peek) == some '?' && isSep (← peekAt 1)
    if explicit then
      adv
      skipBlank
    let e ← flowNode
    skipBlank
    let item ← if (← peek) == some ':' || explicit then
        let v ← if (← peek) == some ':' then flowValueAfterColon else pure Json.null
        match e with
        | .str k => pure (Json.mkObj [(k, v)])
        | _ => fail "mapping-key-error" "a key is not a string"
      else pure e
    items := items.push item
    skipBlank
    match ← peek with
    | some ',' => adv
    | some ']' =>
      adv
      break
    | _ => fail "syntax-error" "expected , or ] in a flow sequence"
  pure (Json.arr items)

partial def flowMap : M Json := do
  adv
  let mut kvs : List (String × Json) := []
  repeat
    skipBlank
    match ← peek with
    | some '}' =>
      adv
      break
    | none => fail "syntax-error" "a flow mapping is not closed"
    | _ => pure ()
    if (← peek) == some '?' && isSep (← peekAt 1) then
      adv
      skipBlank
    let k ← flowNode
    skipBlank
    let v ← if (← peek) == some ':' then flowValueAfterColon else pure Json.null
    match k with
    | .str ks => kvs ← addKey kvs ks v
    | _ => fail "mapping-key-error" "a key is not a string"
    skipBlank
    match ← peek with
    | some ',' => adv
    | some '}' =>
      adv
      break
    | _ => fail "syntax-error" "expected , or } in a flow mapping"
  pure (Json.mkObj kvs)

end

/-! ## Streams -/

def normalise (text : String) : Array Char := Id.run do
  let cs := (if text.startsWith "\uFEFF" then (text.drop 1).toString else text).toList
  let mut out : Array Char := #[]
  let mut prevCr := false
  for c in cs do
    if c == '\r' then
      out := out.push '\n'
      prevCr := true
    else
      unless c == '\n' && prevCr do out := out.push c
      prevCr := false
  pure out

def readLine : M String := do
  let mut r := ""
  repeat
    match ← peek with
    | some c =>
      if c == '\n' then break
      else
        adv
        r := r.push c
    | none => break
  pure r

partial def stream : M (Array Json) := do
  let mut docs : Array Json := #[]
  repeat
    modify fun st => { st with anchors := [], tags := [] }
    skipBlank
    let mut directives := false
    while (← peek) == some '%' && (← col) == 0 do
      let l ← readLine
      directives := true
      if l.startsWith "%YAML" then
        let v := (l.drop 5).toString.trimAscii.toString
        if v.startsWith "1.1" || v.startsWith "1.0" then fail "profile-error" s!"YAML-LD is YAML 1.2; the document says {v}"
      else if l.startsWith "%TAG" && (l.length == 4 || isWs (l.toList[4]!)) then
        match ((l.drop 4).toString.replace "\t" " ").splitOn " " |>.filter (· != "") with
        | [h, pre] =>
          let hs := h.toList
          let okHandle := hs.head? == some '!' && hs.getLast? == some '!' || h == "!"
          unless okHandle do fail "syntax-error" s!"{h} is not a tag handle"
          if (← get).tags.any (·.1 == h) then fail "syntax-error" s!"the tag handle {h} is declared twice"
          if pre.isEmpty then fail "syntax-error" "a %TAG prefix is empty"
          modify fun st => { st with tags := (h, pre) :: st.tags }
        | _ => fail "syntax-error" "%TAG takes a handle and a prefix"
      else fail "profile-error" s!"the directive {l} is not read"
      skipBlank
    if (← peek).isNone then
      if directives then fail "syntax-error" "a directive is not followed by a document"
      break
    let marker ← atDocMarker
    let isStart := marker && (← peek) == some '-'
    if marker && !isStart then
      adv 3
      continue
    if directives && !isStart then fail "syntax-error" "a directive is not followed by ---"
    if isStart then adv 3
    let d ← blockNode (-1) false (!isStart)
    docs := docs.push d
    skipBlank
    if (← peek).isNone then break
    unless (← atDocMarker) do fail "syntax-error" "text follows the document"
  pure docs

/-- Every YAML document of a stream, in order, whatever each holds. -/
def parseAllYaml (text : String) : Except String (Array Json) := do
  let (r, _) ← stream.run { s := normalise text }
  pure r

/-- The first YAML document of a stream, or null when it holds none. -/
def parseYaml (text : String) : Except String Json := do
  pure ((← parseAllYaml text)[0]?.getD Json.null)

/-- A YAML-LD document is a sequence, a mapping or null; any other root is `loading-document-failed` (4.1.3). -/
def checkRoot (d : Json) : Except String Json :=
  match d with
  | .arr _ | .obj _ | .null => .ok d
  | _ => .error "loading-document-failed: the document is a scalar; it must be a mapping, a sequence or null"

/-- Every document of a YAML-LD stream, in order (`extractAllScripts` true). -/
def parseAll (text : String) : Except String (Array Json) := do
  (← parseAllYaml text).mapM checkRoot

/-- The first document of the stream (`extractAllScripts` false). A stream with no document gives null. -/
def parse (text : String) : Except String Json := do
  checkRoot (← parseYaml text)

/-! ## Writing -/

/-- Words a YAML 1.1 reader takes for booleans or null. YAML-LD is read as YAML 1.2, but a document is written so that either reads it. -/
def yaml11Word (s : String) : Bool :=
  ["y", "Y", "yes", "Yes", "YES", "n", "N", "no", "No", "NO", "on", "On", "ON", "off", "Off", "OFF"].contains s

/-- Does a plain scalar of this text read back as the same string, under YAML 1.2 and 1.1 alike? A text that starts like a number or a date is quoted. -/
def plainSafe (s : String) : Bool :=
  let cs := s.toList
  match cs with
  | [] => false
  | c0 :: _ =>
    !(isWs c0) && !(isWs (cs.getLast!)) &&
    !("-?:,[]{}#&*!|>'\"%@`".toList.contains c0) &&
    !(cs.any fun c => c.toNat < 32 || c.toNat == 127 || c == '\u0085' || c == '\u2028' || c == '\u2029') &&
    !(s.splitOn ": ").length > 1 && !(s.splitOn " #").length > 1 && !s.endsWith ":" &&
    !yaml11Word s &&
    !(c0.isDigit || ((c0 == '.' || c0 == '+') && cs.length > 1 && (cs[1]!.isDigit || cs[1]! == '.'))) &&
    (match resolvePlain s with | .ok (.str _) => true | _ => false)

/-- A number with the digits it has: 100.0 stays 100.0, so a double is not turned into an integer. -/
def numberText (n : JsonNumber) : String :=
  let neg := n.mantissa < 0
  let ds := (toString n.mantissa.natAbs)
  let body :=
    if n.exponent == 0 then ds
    else
      let padded := "".pushn '0' (n.exponent + 1 - ds.length) ++ ds
      let cut := padded.length - n.exponent
      (padded.take cut).toString ++ "." ++ (padded.drop cut).toString
  (if neg then "-" else "") ++ body

def scalarText (j : Json) : String :=
  match j with
  | .num n => numberText n
  | .str s => if plainSafe s then s else (Json.str s).compress
  | .null => "null"
  | .arr a => if a.isEmpty then "[]" else ""
  | .obj o => if o.size == 0 then "{}" else ""
  | _ => j.compress

def isFilled : Json → Bool
  | .arr a => !a.isEmpty
  | .obj o => o.size != 0
  | _ => false

def keyText (k : String) : String := if plainSafe k then k else (Json.str k).compress

def pad (n : Nat) : String := "".pushn ' ' n

/-- The lines of a collection at an indent. Mappings list their keys in the order `Json` keeps them: sorted. -/
partial def lines (j : Json) (ind : Nat) : List String :=
  match j with
  | .obj o =>
    o.toList.flatMap fun (k, v) =>
      if isFilled v then (pad ind ++ keyText k ++ ":") :: lines v (ind + 2)
      else [pad ind ++ keyText k ++ ": " ++ scalarText v]
  | .arr a =>
    a.toList.flatMap fun v =>
      if isFilled v then
        match lines v (ind + 2) with
        | first :: rest => (pad ind ++ "- " ++ (first.drop (ind + 2)).toString) :: rest
        | [] => []
      else [pad ind ++ "- " ++ scalarText v]
  | _ => [pad ind ++ scalarText j]

/-- A JSON value as a YAML-LD document in block style, with a newline at the end. -/
def render (j : Json) : String := "\n".intercalate (lines j 0) ++ "\n"

/-- The text of a file, or why it could not be read. A file that is not UTF-8 is refused (`invalid-encoding`, 4.1.1). -/
def readText (path : String) : IO (Except String String) := do
  match ← (IO.FS.readFile (System.FilePath.mk path)).toBaseIO with
  | .ok text => pure (.ok text)
  | .error e => pure (.error s!"invalid-encoding or unreadable: {path}: {e}")

/-- The first YAML-LD document of a file (`extractAllScripts` false). -/
def readFile (path : String) : IO (Except String Json) := do
  match ← readText path with
  | .error e => pure (.error e)
  | .ok t => pure (match parse t with | .ok j => .ok j | .error e => .error s!"{path}: {e}")

end YamlLd
