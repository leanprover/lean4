import Std.Http

open Std Http
open Std.Http.Protocol.H1

/-!
Tests chunk-size lines with extensions that arrive in pieces. While such a line arrives, the reader
follows the chunk-extension grammar byte by byte (`LineScan`) and parses the line again only when a
byte may end it, fail it, or pass a limit. Every input below gives the same answer when read whole,
in any two reads, and one byte per read (compared with the prefix read at once after every byte):
extension names and values, `BWS` in each place, quoted values and their escapes, the limits on
names, values, whitespace, extensions and line length, and malformed lines.
-/

def check (cond : Bool) (msg : String) : IO Unit :=
  unless cond do throw (IO.userError msg)

/-- Runs the machine until it stops making progress, collecting its output. -/
def settle (m : Machine dir) (out : ByteArray) : Machine dir × ByteArray := Id.run do
  let mut m := m
  let mut out := out
  for _ in [0:8] do
    let (m', r) := m.step
    m := m'
    out := out ++ r.output.toByteArray
    while m.canPullBody do
      let (m', chunk?) := m.pullBody
      m := m'
      if chunk?.isNone then break
  (m, out)

def small : Protocol.H1.Config :=
  { maxSpaceSequence := 3, maxChunkExtNameLength := 4, maxChunkExtValueLength := 5,
    maxChunkExtensions := 2, maxChunkLineLength := 40 }

/-- A server's state after reads: its error, output, and whether it waits for input. -/
def serverStart (config : Protocol.H1.Config) : Machine .receiving := { config }

def clientStart (config : Protocol.H1.Config) : Machine .sending :=
  ({ config } : Machine .sending).send
    { method := .get, version := .v11, uri := RequestTarget.originForm! "/",
      headers := Headers.empty.insert! "Host" "a" } |>.userClosedBody

def view (m : Machine dir) (out : ByteArray) : Option Error × String × Bool :=
  (m.error, String.fromUTF8Lossy out, m.isReaderComplete || m.isReaderClosed)

def feedAll (m : Machine dir) (parts : List ByteArray) : Option Error × String × Bool := Id.run do
  let mut m := m
  let mut out := ByteArray.empty
  for p in parts do
    (m, out) := settle (m.feed p) out
  view m out

/-- Whole, every 2-read split, and one byte per read (after every byte) agree. -/
def invariant (who : String) (start : Machine dir) (input : ByteArray) : IO Unit := do
  let whole := feedAll start [input]
  for i in [1:input.size] do
    let split := feedAll start [input.extract 0 i, input.extract i input.size]
    check (split == whole)
      s!"{who}: split at {i} gives {repr split}, one read gives {repr whole}"
  let mut m := start
  let mut out := ByteArray.empty
  for i in [0:input.size] do
    (m, out) := settle (m.feed (input.extract i (i + 1))) out
    let once := feedAll start [input.extract 0 (i + 1)]
    check (view m out == once)
      s!"{who}: after {i + 1} bytes, one byte per read gives {repr (view m out)}, one read gives {repr once}"

def lines : List String := [
  "1;a=b;c;d=\"x y\";e = f ;g", "1 ;a", "1;a ", "1;a=b ", "1 ", "1;a=\"q\\\"\\\\w\";b=c",
  "1;a=\"\xc3\xa9\"", "1;a=\"unterminated", "1;a=\"x\\\x01\"", "1;=b", "1;;a", "1;a=", "1;a=\"x\"y",
  "1;a=b,c", "1;a=\"x\";b", "1;a=\"x\" ;b", "1;a=\"x\" ", "0001;a=b", "00000000000000000001",
  "11111111111111111", "1111111111111111", "1;a;b;c", "1;a=b;c=d;e=\"f\"", "1;a;b;c=ddddd",
  "1;a;b=ddddd", "1;a=bbbbb;c", "1;a=bbbbbb", "1;aaaa=b", "1;aaaaa=b", "1;   a", "1;    a",
  "1;a   =b", "1;a    =b", "1;a=   b", "1;a=    b", "1   ;a", "1    ;a", "1;a=\"bbbbb\"", "1;a=\"bbbbbb\"",
  "1;a=\"bbbb\\b\"", "1;a=\"bbbbb\\b\"", "1;abc=de;fg=h;" ++ String.ofList (List.replicate 40 'x'),
  "1;a\t=\tb", "1;a=b\t;c", "1\r", "1;a\r"]

def request (line : String) : ByteArray :=
  s!"POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n{line}\r\na\r\n0\r\n\r\n".toUTF8

def response (line : String) : ByteArray :=
  s!"HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n{line}\r\na\r\n0\r\n\r\n".toUTF8

def runCases (cases : List (IO Unit)) : IO Unit := do
  let mut errors : Array String := #[]
  for c in cases do
    try c catch e => errors := errors.push (toString e)
  unless errors.isEmpty do throw (IO.userError ("\n".intercalate errors.toList))

#eval runCases <| lines.flatMap fun line =>
  [{}, small].flatMap fun (config : Protocol.H1.Config) =>
    let name := s!"{line.quote} (maxChunkExtensions {config.maxChunkExtensions})"
    [invariant s!"server {name}" (serverStart config) (request line),
     invariant s!"client {name}" (clientStart config) (response line)]
