import Std.Http

open Std Http
open Std.Http.Protocol.H1

/-!
Differential test for the request-line and header-line fast paths of the HTTP/1.1 parser
(`parseRequestLineFast`, `parseHeaderLineFast`): whenever a fast path accepts its input, the general
parser (`parseRequestLineRawVersion`, `parseSingleHeader` followed by `Header.Name.ofString?` and
`Header.Value.ofString?`) must accept the same bytes with the same result and end position. Common
request and header lines must take the fast path.
-/

/-- The general request-line parser: method, target (as `repr`), version and end position. -/
private def generalRequestLine (bytes : ByteArray) : Option (Method × String × Option Version × Nat) :=
  match parseRequestLineRawVersion {} bytes.iter with
  | .success it (method, target, version) => some (method, reprStr target, version, it.pos)
  | .error .. => none

/-- The request-line fast path, in the shape of `generalRequestLine`. -/
private def fastRequestLine (bytes : ByteArray) : Option (Method × String × Option Version × Nat) :=
  match parseRequestLineFast {} bytes 0 with
  | .line method target version stop => some (method, reprStr target, some version, stop)
  | .fallback => none

/--
The general header-line parser followed by the typing the server applies: the lowercase name and
value, or `none` for the blank line, and the end position. `none` if parsing or typing fails.
-/
private def generalHeaderLine (bytes : ByteArray) : Option (Option (String × String) × Nat) :=
  match parseSingleHeader {} bytes.iter with
  | .success it none => some (none, it.pos)
  | .success it (some (name, value)) =>
    match Header.Name.ofString? name, Header.Value.ofString? value with
    | some name, some value => some (some (name.value, value.value), it.pos)
    | _, _ => none
  | .error .. => none

/-- The header-line fast path, in the shape of `generalHeaderLine`. -/
private def fastHeaderLine (bytes : ByteArray) : Option (Option (String × String) × Nat) :=
  match parseHeaderLineFast {} bytes 0 with
  | .field name value stop => some (some (name.value, value.value), stop)
  | .endOfHeaders stop => some (none, stop)
  | .fallback => none

/-- Fails unless `general` agrees with `fast` whenever the fast path accepted the input. -/
private def agree [BEq α] [Repr α] (what : String) (bytes : ByteArray) (fast general : Option α) :
    IO Unit := do
  if let some f := fast then
    unless general == some f do
      throw <| IO.userError <|
        s!"{what}: fast path disagrees with the general parser on {repr bytes.toList}\n" ++
        s!"  fast: {repr f}\n  general: {repr general}"

private def nextSeed (seed : Nat) : Nat :=
  (seed * 1103515245 + 12345) % 2147483648

private def pick (seed : Nat) (xs : Array String) : String × Nat :=
  let seed := nextSeed seed
  (xs[seed % xs.size]!, seed)

private def noise : Array UInt8 :=
  #[32, 9, 58, 13, 10, 37, 63, 47, 61, 38, 44, 65, 97, 48, 0, 127, 255]

/-- Overwrites up to two random bytes of `bytes` with delimiter-like or invalid bytes. -/
private def mutate (seed : Nat) (bytes : ByteArray) : ByteArray × Nat := Id.run do
  let mut seed := nextSeed seed
  let mut bytes := bytes
  let count := seed % 3
  for _ in *...count do
    if bytes.size == 0 then
      break
    seed := nextSeed seed
    let pos := seed % bytes.size
    seed := nextSeed seed
    bytes := bytes.set! pos (noise[seed % noise.size]!)
  return (bytes, seed)

private def methods : Array String :=
  #["GET", "POST", "PUT", "HEAD", "DELETE", "PATCH", "OPTIONS", "TRACE", "CONNECT", "PROPFIND",
    "get", "GETS", "POS", ""]

private def targets : Array String :=
  #["/", "/a", "/api/v1/items", "/a//b", "/a/", "/%41%62", "/%4", "/%zz", "/a?b=c", "/a?b=c&d",
    "/a?=x&&y=", "/search?q=lean+prover&lang=en", "/a?b=c=d", "/a?", "/a b", "*",
    "http://h.example/x", "example.com:443", "/a#frag", "//x", "/a;p=1", "/~user/it's", "/é", ""]

private def versions : Array String :=
  #["HTTP/1.1", "HTTP/1.1", "HTTP/1.0", "HTTP/2.0", "HTTP/1.2", "http/1.1", "HTTP/11", "HTTP/1.", ""]

private def separators : Array String :=
  #[" ", " ", " ", "  ", "\t"]

private def lineEnds : Array String :=
  #["\r\n", "\r\n", "\r\n", "\n", "\r", "", "\r\nGET"]

private def names : Array String :=
  #["Host", "host", "HOST", "Content-Length", "content-type", "X-Custom", "x_y.z", "Bad Name", "",
    "Ünï", "Accept-Encoding", "TE", "Set-Cookie", "!#$%&'*+-.^_`|~"]

private def colons : Array String :=
  #[":", ": ", ": ", ":  ", ":\t", " :", "::"]

private def values : Array String :=
  #["example.com", "", "42", "text/html; charset=utf-8", "a\tb", "a, b", "trail ", "trail\t ", "\x7f",
    "é", "q=0.9, */*"]

#eval show IO Unit from do
  for line in #["GET / HTTP/1.1\r\n", "POST /api/items?id=7&x HTTP/1.0\r\n", "DELETE /a/b/ HTTP/1.1\r\n",
      "GET /search?q=lean+prover&lang=en HTTP/1.1\r\n"] do
    let bytes := line.toUTF8
    unless (fastRequestLine bytes).isSome do
      throw <| IO.userError s!"request line {repr line} should take the fast path"
    agree "request line" bytes (fastRequestLine bytes) (generalRequestLine bytes)
  for line in #["Host: example.com\r\n", "Content-Length: 42\r\n", "X-Custom:  padded value \t\r\n",
      "accept-encoding: gzip, deflate\r\n", "\r\n"] do
    let bytes := line.toUTF8
    unless (fastHeaderLine bytes).isSome do
      throw <| IO.userError s!"header line {repr line} should take the fast path"
    agree "header line" bytes (fastHeaderLine bytes) (generalHeaderLine bytes)

#eval show IO Unit from do
  let mut seed := 20261028
  let mut fastHits := 0
  for _ in *...4000 do
    let (method, s1) := pick seed methods
    let (sep1, s2) := pick s1 separators
    let (target, s3) := pick s2 targets
    let (sep2, s4) := pick s3 separators
    let (version, s5) := pick s4 versions
    let (lineEnd, s6) := pick s5 lineEnds
    let bytes := (method ++ sep1 ++ target ++ sep2 ++ version ++ lineEnd).toUTF8
    let (mutated, s7) := mutate s6 bytes
    seed := s7
    for input in #[bytes, mutated] do
      let fast := fastRequestLine input
      if fast.isSome then
        fastHits := fastHits + 1
      agree "request line" input fast (generalRequestLine input)
  unless fastHits > 0 do
    throw <| IO.userError "no generated request line took the fast path"

#eval show IO Unit from do
  let mut seed := 15887
  let mut fastHits := 0
  for _ in *...4000 do
    let (name, s1) := pick seed names
    let (colon, s2) := pick s1 colons
    let (value, s3) := pick s2 values
    let (lineEnd, s4) := pick s3 lineEnds
    let bytes := (name ++ colon ++ value ++ lineEnd).toUTF8
    let (mutated, s5) := mutate s4 bytes
    seed := s5
    for input in #[bytes, mutated] do
      let fast := fastHeaderLine input
      if fast.isSome then
        fastHits := fastHits + 1
      agree "header line" input fast (generalHeaderLine input)
  unless fastHits > 0 do
    throw <| IO.userError "no generated header line took the fast path"
