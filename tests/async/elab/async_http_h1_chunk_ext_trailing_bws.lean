import Std.Http

open Std Http
open Std.Http.Protocol.H1

/-!
Tests that whitespace after a chunk-extension name without a value, at the end of a chunk-size line,
is rejected. RFC 9112 §7.1.1 allows BWS after a name only before `=`
(`chunk-ext = *( BWS ";" BWS chunk-ext-name [ BWS "=" BWS chunk-ext-val ] )`), so `5;a \r\n` is as
malformed as `5 \r\n` and `5;a=b \r\n`, which were already rejected, while `5;a ;b`, `5;a = b` and
`5 ;a` stay valid. Each input is checked whole, as every 2-read split, and as every prefix fed one
byte per read, by a server and by a client.
-/

def check (cond : Bool) (msg : String) : IO Unit :=
  unless cond do throw (IO.userError msg)

/-- Runs the machine until it stops making progress, collecting its output and the body. -/
def settle (m : Machine dir) (out body : ByteArray) : Machine dir × ByteArray × ByteArray := Id.run do
  let mut m := m
  let mut out := out
  let mut body := body
  for _ in [0:8] do
    let (m', r) := m.step
    m := m'
    out := out ++ r.output.toByteArray
    while m.canPullBody do
      let (m', chunk?) := m.pullBody
      m := m'
      match chunk? with
      | some c => body := body ++ c.chunk.data
      | none => break
  (m, out, body)

/-- The error, the output and the body after a server reads `parts`. -/
def server (parts : List ByteArray) : Option Error × String × String := Id.run do
  let mut m : Machine .receiving := { config := {} }
  let mut out := ByteArray.empty
  let mut body := ByteArray.empty
  for p in parts do
    (m, out, body) := settle (m.feed p) out body
  (m.error, String.fromUTF8! out, String.fromUTF8! body)

/-- The error and the body after a client that sent a GET reads `parts` as the response. -/
def client (parts : List ByteArray) : Option Error × String × String := Id.run do
  let mut m : Machine .sending := ({ config := {} } : Machine .sending).send
    { method := .get, version := .v11, uri := RequestTarget.originForm! "/",
      headers := Headers.empty.insert! "Host" "a" } |>.userClosedBody
  let mut out := ByteArray.empty
  let mut body := ByteArray.empty
  for p in parts do
    (m, out, body) := settle (m.feed p) out body
  (m.error, "", String.fromUTF8! body)

def chunkedRequest (line : String) : ByteArray :=
  s!"POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n{line}\r\nhello\r\n0\r\n\r\n".toUTF8

def chunkedResponse (line : String) : ByteArray :=
  s!"HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n{line}\r\nhello\r\n0\r\n\r\n".toUTF8

/--
`run input` read whole must give `expected` (`none`: read with body `hello`; `some e`: fail with
`e`), and so must every 2-read split. Every prefix fed one byte per read must fail or wait as that
prefix read whole does (the body delivered so far may differ: the last bytes of a chunk wait for the
line break after them).
-/
def sameEverywhere (name : String) (run : List ByteArray → Option Error × String × String)
    (input : ByteArray) (expected : Option Error) : IO Unit := do
  let whole := run [input]
  let ok := if expected.isNone then whole.1.isNone && whole.2.2 == "hello" else whole.1 == expected
  check ok s!"{name}: expected {repr expected} (none: the body hello), got {repr whole.1} {whole.2.2.quote}"
  for i in [1:input.size] do
    let split := run [input.extract 0 i, input.extract i input.size]
    check (split == whole) s!"{name}: a split after byte {i} gives {repr split.1}, whole gives {repr whole.1}"
  for i in [1:input.size + 1] do
    let pre := input.extract 0 i
    let drip := run ((List.range i).map fun j => pre.extract j (j + 1))
    let once := run [pre]
    check (drip.1 == once.1 && drip.2.1 == once.2.1)
      s!"{name}: the first {i} bytes one per read give {repr drip.1}, one read gives {repr once.1}"

/-- Runs every case and throws once, listing the failures. -/
def runCases (cases : List (IO Unit)) : IO Unit := do
  let mut errors : Array String := #[]
  for c in cases do
    try c catch e => errors := errors.push (toString e)
  unless errors.isEmpty do throw (IO.userError ("\n".intercalate errors.toList))

def rejected : List String :=
  ["5;a ", "5;a\t", "5;a  \t ", "5;a=b;c ", "5;a;b ", "5 ", "5;a=b ", "5;a=\"b\" "]

def accepted : List String :=
  ["5;a", "5;a ;b", "5;a\t;b", "5;a =b", "5;a= b", "5;a = b", "5 ;a", "5;a=b;c", "5;a=\"b\";c",
    "5;a ;b=c"]

/-- The status a server answers a last chunk whose extension has trailing BWS with. -/
def lastChunkStatus : IO Unit := do
  let (err, out, _) := server
    ["POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n0;a \r\n\r\n".toUTF8]
  check (err == some .badMessage && out.startsWith "HTTP/1.1 400 ")
    s!"last chunk 0;a: expected 400, got {repr err} {out.quote}"

#eval runCases <|
  (rejected.map fun line => sameEverywhere s!"server {line.quote}" server (chunkedRequest line)
    (some .badMessage)) ++
  (accepted.map fun line => sameEverywhere s!"server {line.quote}" server (chunkedRequest line) none) ++
  (rejected.map fun line => sameEverywhere s!"client {line.quote}" client (chunkedResponse line)
    (some .badMessage)) ++
  (accepted.map fun line => sameEverywhere s!"client {line.quote}" client (chunkedResponse line) none) ++
  [lastChunkStatus]
