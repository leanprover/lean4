import Std.Http

open Std Http
open Std.Http.Protocol.H1

/-!
Tests that chunked framing counts toward `maxBodySize`: chunk-size lines with their extensions, the
line break after each chunk's data, and the trailer section. Otherwise a body of small chunks with
long extensions makes the server read many times `maxBodySize` from the network for a body that
fits the limit.
-/

/--
Feeds `data` to a server machine `piece` bytes at a time, pulling the body as it arrives. Returns
the machine's error, whether the body completed, and the number of content bytes pulled.
-/
def run (config : Protocol.H1.Config) (data : ByteArray) (piece : Nat) :
    Option Error × Bool × Nat := Id.run do
  let mut m : Machine .receiving := { config }
  let mut pulled := 0
  let mut complete := false
  let mut i := 0
  while i < data.size && !m.failed do
    m := m.feed (data.extract i (i + piece))
    i := i + piece
    for _ in [0:4] do
      m := m.step.1
      let (m', chunk) := m.pullBody
      m := m'
      if let some c := chunk then
        pulled := pulled + c.chunk.data.size
        complete := complete || c.final
  return (m.error, complete, pulled)

def chunkedPost : String :=
  "POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n"

-- 1000 one-byte chunks with ~100-byte extensions: 1000 content bytes, over 100 KB on the wire.
#eval show IO Unit from do
  let ext := s!";name={String.ofList (List.replicate 100 'x')}"
  let body := String.join (List.replicate 1000 s!"1{ext}\r\nX\r\n") ++ "0\r\n\r\n"
  let (error, complete, pulled) := run { maxBodySize := 2000 } (chunkedPost ++ body).toUTF8 4096
  unless error == some .entityTooLarge && !complete && pulled < 2000 do
    throw <| IO.userError s!"framing not counted: {repr error}, complete {complete}, pulled {pulled}"

-- The limit is exactly the body's wire size: it fits, and one byte less does not, however the
-- input is split. The last byte over the limit is the line break that ends the trailer section.
#eval show IO Unit from do
  let body := "5\r\nhello\r\n3;x=y\r\nabc\r\n0\r\nX-Trace: 1\r\n\r\n"
  let data := (chunkedPost ++ body).toUTF8
  for piece in [data.size, 1] do
    let (error, complete, pulled) := run { maxBodySize := body.utf8ByteSize } data piece
    unless error.isNone && complete && pulled == 8 do
      throw <| IO.userError s!"exact fit, pieces of {piece}: {repr error}, complete {complete}, pulled {pulled}"
    let (error, complete, _) := run { maxBodySize := body.utf8ByteSize - 1 } data piece
    unless error == some .entityTooLarge && !complete do
      throw <| IO.userError s!"one byte over, pieces of {piece}: {repr error}, complete {complete}"
