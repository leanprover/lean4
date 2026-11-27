import Std.Http

open Std Internal Parsec ByteArray
open Std.Http Std.Http.Protocol.H1

/-!
Checks the request line that `parseRequestLine` reads with byte scans against independent references:
the method against a lookup in `Method.all` by name, and the request-target against
`URI.Parser.parseRequestTarget` run on the same bytes, over generated targets that are mostly
origin-form (the scanned path) and partly the other forms, malformed escapes and queries. Also checks
`maxPathSegments` and `maxQueryParams`, and `Header.Name.ofAsciiBytes?` against `Header.Name.ofString?`.
-/

/-- A small deterministic generator. -/
def next (s : Nat) : Nat := (s * 1103515245 + 12345) % 2147483648

def below (s n : Nat) : Nat × Nat :=
  let s := next s
  (s % n, s)

def runLine (c : Protocol.H1.Config) (line : String) : Except String Request.Head :=
  (parseRequestLine c).run line.toUTF8

/-! ## Methods -/

/-- The reference method of a token: the `Method` with that exact name. -/
def methodOf? (token : String) : Option Method :=
  Method.all.find? (toString · == token)

def checkMethod (token : String) : Except String Unit := do
  match runLine {} s!"{token} /a HTTP/1.1\r\n", methodOf? token with
  | .ok head, some m =>
    unless head.method == m do throw s!"{token.quote}: read as {head.method}, expected {m}"
  | .error e, none =>
    unless (e.splitOn "unrecognized method").length > 1 do
      throw s!"{token.quote}: unexpected error {e}"
  | .ok head, none => throw s!"{token.quote}: read as {head.method}, expected unrecognized"
  | .error e, some m => throw s!"{token.quote}: error {e}, expected {m}"

def methodChecks : Except String Unit := do
  for m in Method.all do
    checkMethod (toString m)
    -- A prefix or an extension of a method, and its lowercase, are other tokens.
    checkMethod ((toString m).dropEnd 1).toString
    checkMethod (toString m ++ "X")
    checkMethod (toString m).toLower
  let alphabet := #["G", "E", "T", "P", "O", "S", "-", "A", "C", "L", "!", "x", "7", "~"]
  let mut s := 11
  for _ in [0:400] do
    let (n, s') := below s 12
    s := s'
    let mut token := ""
    for _ in [0:n + 1] do
      let (i, s') := below s alphabet.size
      s := s'
      token := token ++ alphabet[i]!
    checkMethod token
  -- A token of `maxMethodLength` bytes or more is skipped to its end before the line is read.
  for n in [maxMethodLength - 1, maxMethodLength, maxMethodLength + 1, 300] do
    checkMethod (String.ofList (List.replicate n 'A'))
  -- A token followed by a byte other than SP fails: an unrecognized one as an invalid method. A
  -- token cut off needs more input.
  match runLine {} "GET\t/ HTTP/1.1\r\n" with
  | .error _ => pure ()
  | .ok _ => throw "GET\\t: accepted"
  match runLine {} "BREW\t/ HTTP/1.1\r\n" with
  | .error e => unless (e.splitOn "invalid method").length > 1 do throw s!"BREW\\t: {e}"
  | .ok _ => throw "BREW\\t: accepted"
  match (parseRequestLine {}) "GE".toUTF8.iter with
  | .error _ .eof => pure ()
  | _ => throw "GE: expected .eof"

/-! ## Request targets -/

/-- `parseRequestTarget` with the limits `parseRequestLine` gives it under `Config` `{}`. -/
def referenceTarget (target : String) : Except String RequestTarget :=
  let n := ({} : Protocol.H1.Config).maxUriLength
  let config : URI.Config :=
    { maxSchemeLength := n, maxUserInfoLength := n, maxSegmentLength := n, maxQueryLength := n,
      maxFragmentLength := n, maxPathSegments := n, maxTotalPathLength := n, maxQueryParams := n }
  (URI.Parser.parseRequestTarget config <* eof).run target.toUTF8

/-- Pieces of request-targets: every byte is one `parseRequestLine` reads as part of the target. -/
def pieces : Array String :=
  #["/", "/", "/", "a", "Zz", "09", "-", ".", "_", "~", "%", "%2F", "%zz", "%4", "%41", "?", "&", "=",
    ":", "@", "!", "$", "'", "(", ")", "*", "+", ",", ";", "[", "]", "//", "?a=b", "&&", "==", "..",
    "http:", "//h", "x.y:80"]

def templates : Array String :=
  #["/", "//", "/a/", "/a//b", "/?", "/a?b", "/a?=", "/a?&", "/a?b=c=d", "/a?b&c=d&", "/%41/%2f", "/a%2",
    "/?%zz", "/a?b%3", "/[x]", "/a?[", "/?=&=", "/pipeline", "/baseline11?a=13&b=42", "*",
    "http://h/p?q", "h:80", "/a?b?c/d"]

def randomTarget (seed : Nat) : String := Id.run do
  let mut s := seed
  let (n, s') := below s 10
  s := s'
  let (origin, s') := below s 10
  s := s'
  let mut out := if origin < 9 then "/" else ""
  for _ in [0:n] do
    let (i, s') := below s pieces.size
    s := s'
    out := out ++ pieces[i]!
  return out

def checkTarget (target : String) : Except String Unit := do
  match runLine {} s!"GET {target} HTTP/1.1\r\n", referenceTarget target with
  | .ok head, .ok ref =>
    unless reprStr head.uri == reprStr ref do
      throw s!"{target.quote}: read as {reprStr head.uri}, expected {reprStr ref}"
  | .error e, .error ref =>
    unless (e.splitOn ref).length > 1 do throw s!"{target.quote}: error {e}, expected {ref}"
  | .ok head, .error ref => throw s!"{target.quote}: read as {reprStr head.uri}, expected error {ref}"
  | .error e, .ok ref => throw s!"{target.quote}: error {e}, expected {reprStr ref}"

def targetChecks : Except String Unit := do
  for t in templates do checkTarget t
  for i in [0:3000] do checkTarget (randomTarget (i * 7919 + 3))

/-- Path segments and query parameters past the configured counts make the target too long. -/
def limitChecks : Except String Unit := do
  let c : Protocol.H1.Config := { maxPathSegments := some 2, maxQueryParams := some 1 }
  for (target, ok) in [("/a/b", true), ("/a/b/c", false), ("/a/", true), ("/a//", false),
      ("/?x=1", true), ("/?x=1&y", false), ("/a?&", false), ("/a/b?q", true)] do
    match runLine c s!"GET {target} HTTP/1.1\r\n" with
    | .ok _ => unless ok do throw s!"{target}: accepted over the limits"
    | .error e =>
      if ok then throw s!"{target}: {e}"
      unless (e.splitOn "uri too long").length > 1 do throw s!"{target}: {e}"

/-! ## Header names from bytes -/

def nameChecks : Except String Unit := do
  let alphabet := #["a", "Z", "-", "0", "!", "#", "$", "%", "&", "'", "*", "+", ".", "^", "_", "`",
    "|", "~", "Content", "TYPE", " ", ":", "\t", "(", "\"", "é", "\x7f"]
  let mut s := 5
  for _ in [0:2000] do
    let (n, s') := below s 8
    s := s'
    let mut name := ""
    for _ in [0:n] do
      let (i, s') := below s alphabet.size
      s := s'
      name := name ++ alphabet[i]!
    -- The bytes `parseHeaderField` hands over are a token without whitespace around it.
    let expected := if name.any Char.isWhitespace then none else Header.Name.ofString? name
    let got := Header.Name.ofAsciiBytes? name.toUTF8
    unless (got.map (·.value)) == (expected.map (·.value)) do
      throw s!"{name.quote}: {repr (got.map (·.value))}, expected {repr (expected.map (·.value))}"

def main : IO Unit := do
  for (name, check) in [("methods", methodChecks), ("targets", targetChecks),
      ("limits", limitChecks), ("names", nameChecks)] do
    match check with
    | .ok () => pure ()
    | .error e => throw <| IO.userError s!"{name}: {e}"

#eval main
