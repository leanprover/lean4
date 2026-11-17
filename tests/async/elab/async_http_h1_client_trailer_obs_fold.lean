import Std.Http

open Std Http
open Std.Http.Protocol.H1

/-!
Tests that a client accepts an obs-fold in the trailer section of a chunked response. RFC 9112 §5.2
says a user agent that receives an obs-fold in a response MUST replace it with SP, and a client
discards trailer fields, so the folded line is read with the field it continues. The body, the end of
the response and the next exchange on the connection are unchanged. A trailer section that starts
with whitespace continues no field and still fails, and a server still rejects a folded request
trailer with 400. Each response is read whole, one byte per read, split into two reads at every
point, and cut short at every point.
-/

def check (cond : Bool) (msg : String) : IO Unit :=
  unless cond do throw (IO.userError msg)

def get : Request.Head :=
  { method := .get, version := .v11, uri := RequestTarget.originForm! "/",
    headers := Headers.empty.insert! "Host" "a" }

/-- Runs the machine until it stops making progress, collecting the body and the response heads. -/
def settle (m : Machine .sending) (body : ByteArray) (heads : Nat) :
    Machine .sending × ByteArray × Nat := Id.run do
  let mut m := m
  let mut body := body
  let mut heads := heads
  for _ in [0:16] do
    let (m', r) := m.step
    m := m'
    for e in r.events do
      if e matches .endHeaders _ then heads := heads + 1
    while m.canPullBody do
      let (m', chunk?) := m.pullBody
      m := m'
      match chunk? with
      | some c => body := body ++ c.chunk.data
      | none => break
  (m, body, heads)

structure Run where
  error : Option Error
  body : String
  heads : Nat
  next : Bool
deriving BEq, Repr

/-- Sends a GET, reads `parts`, then sends a second GET and reads a response with body `b`. -/
def run (parts : List ByteArray) (second := true) : Run := Id.run do
  let mut m : Machine .sending := ({ config := {} } : Machine .sending).send get |>.userClosedBody
  let mut body := ByteArray.empty
  let mut heads := 0
  for p in parts do
    (m, body, heads) := settle (m.feed p) body heads
  let mut next := false
  if second && m.isWaitingMessage then
    (m, body, heads) := settle (m.send get |>.userClosedBody) body heads
    (m, body, heads) := settle (m.feed "HTTP/1.1 200 OK\r\nContent-Length: 1\r\n\r\nb".toUTF8) body heads
    next := m.error.isNone
  { error := m.error, body := String.fromUTF8! body, heads, next }

def readings (b : ByteArray) : List (List ByteArray) :=
  [b] :: (List.range b.size).map (fun i => b.extract i (i + 1)) ::
    (List.range (b.size - 1)).map fun i => [b.extract 0 (i + 1), b.extract (i + 1) b.size]

def accepts (name : String) (trailers : String) : IO Unit := do
  let input := ("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n2\r\nhi\r\n0\r\n" ++ trailers).toUTF8
  let expected : Run := { error := none, body := "hib", heads := 2, next := true }
  for parts in readings input do
    let r := run parts
    check (r == expected) s!"{name}, {parts.length} read(s): expected {repr expected}, got {repr r}"
  for i in [1:input.size] do
    let r := run [input.extract 0 i] (second := false)
    check r.error.isNone s!"{name}: the prefix of {i} bytes fails with {repr r.error}"

def rejects (name : String) (trailers : String) : IO Unit := do
  let input := ("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n2\r\nhi\r\n0\r\n" ++ trailers).toUTF8
  for parts in readings input do
    let r := run parts (second := false)
    check (r.error == some .badMessage) s!"{name}, {parts.length} read(s): expected a failure, got {repr r}"

/-- A server reads `request` and answers with its error status, or `none`. -/
def serverStatus (request : String) : Option Nat := Id.run do
  let mut m : Machine .receiving := ({ config := {} } : Machine .receiving).feed request.toUTF8
  let mut out := ByteArray.empty
  for _ in [0:16] do
    let (m', r) := m.step
    m := m'
    out := out ++ r.output.toByteArray
    while m.canPullBody do
      let (m', chunk?) := m.pullBody
      m := m'
      if chunk?.isNone then break
  let text := String.fromUTF8! out
  if text.startsWith "HTTP/1.1 " then (text.drop 9 |>.take 3 |>.toString).toNat? else none

def runCases (cases : List (IO Unit)) : IO Unit := do
  let mut errors : Array String := #[]
  for c in cases do
    try c catch e => errors := errors.push (toString e)
  unless errors.isEmpty do throw (IO.userError ("\n".intercalate errors.toList))

#eval runCases [
  accepts "no trailers" "\r\n",
  accepts "plain trailer" "T: v\r\n\r\n",
  accepts "folded with SP" "T: v\r\n w\r\n\r\n",
  accepts "folded with HTAB" "T: v\r\n\tw\r\n\r\n",
  accepts "folded twice, then a field" "T: v\r\n w\r\n  x y\r\nU: 1\r\n\r\n",
  accepts "fold of only whitespace" "T: v\r\n \r\n\r\n",
  accepts "folded discarded field" "Authorization: x\r\n y\r\n\r\n",
  rejects "whitespace before the first trailer field" " T: v\r\n\r\n",
  rejects "folded reframing field" "Content-Length: 1\r\n 2\r\n\r\n",
  do
    let status := serverStatus
      "POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n0\r\nT: v\r\n w\r\n\r\n"
    check (status == some 400) s!"server: a folded request trailer should get 400, got {status}"]
