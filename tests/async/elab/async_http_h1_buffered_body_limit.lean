import Std.Http

open Std Http
open Std.Http.Protocol.H1

/-!
Tests `Config.maxBufferedBodyBytes`, which bounds the unread input a machine keeps in memory apart
from `maxBodySize`: a client allowing a body of any length still fails input buffered ahead of its
reader past the bound, a reader that keeps pulling never reaches it, and without it the bound comes
from `maxBodySize` as before.
-/

def getHead : Request.Head :=
  { method := .get, version := .v11, uri := RequestTarget.parse! "/",
    headers := Headers.empty.insert .host (.mk "a") }

def bodySize : Nat := 128 * 1024

def responseHead : ByteArray :=
  s!"HTTP/1.1 200 OK\r\nContent-Length: {bodySize}\r\n\r\n".toUTF8

def body : ByteArray := ⟨Array.replicate bodySize 'x'.toUInt8⟩

/-- A client machine that has written a GET and waits for its response. -/
def sentGet (config : Protocol.H1.Config) : Machine .sending := Id.run do
  let mut machine : Machine .sending := { config }
  machine := machine.send getHead |>.userClosedBody
  for _ in [0:4] do
    machine := machine.step.1
  return machine

def unbounded : Nat := 2 ^ 64

/-- `maxBufferedBodyBytes` plus the default header, start-line and chunk-line allowances. -/
def bound (bodyBytes : Nat) : Nat :=
  let config : Protocol.H1.Config := {}
  bodyBytes + config.maxHeaderBytes + config.maxStartLineLength + config.maxChunkLineLength

-- The whole response in one read is far past a 1 KiB bound, even though `maxBodySize` allows it.
#guard
  let machine := (sentGet { maxBodySize := unbounded, maxBufferedBodyBytes := some 1024 }).feed
    (responseHead ++ body)
  machine.error == some .entityTooLarge

-- The bound counts every unread byte, the head included: one byte past it fails, and up to it does not.
#guard
  let config : Protocol.H1.Config := { maxBodySize := unbounded, maxBufferedBodyBytes := some 1024 }
  let input := responseHead ++ body
  (sentGet config |>.feed (input.extract 0 (bound 1024))).error.isNone &&
    (sentGet config |>.feed (input.extract 0 (bound 1024 + 1))).error == some .entityTooLarge

/-- Feeds the response in reads of `readSize` bytes, stepping and pulling the body after each one,
and returns the machine's error and the body bytes pulled. -/
def readInPieces (config : Protocol.H1.Config) (readSize : Nat) : Option Error × Nat := Id.run do
  let input := responseHead ++ body
  let mut machine := sentGet config
  let mut pulled := 0
  let mut offset := 0
  while offset < input.size do
    machine := machine.feed (input.extract offset (offset + readSize))
    offset := offset + readSize
    for _ in [0:4] do
      machine := machine.step.1
      while machine.canPullBodyNow do
        let (next, chunk?) := machine.pullBody
        machine := next
        if let some chunk := chunk? then
          pulled := pulled + chunk.chunk.data.size
  return (machine.error, pulled)

-- A reader that keeps pulling stays under the bound, and gets the whole body.
#guard readInPieces { maxBodySize := unbounded, maxBufferedBodyBytes := some 1024 } (16 * 1024) ==
  (none, bodySize)

-- Without `maxBufferedBodyBytes`, `maxBodySize` sets the bound, so an unbounded body buffers freely.
#guard ((sentGet { maxBodySize := unbounded }).feed (responseHead ++ body)).error.isNone

-- And a `maxBodySize` smaller than the body still bounds the buffer by itself.
#guard ((sentGet { maxBodySize := 1024 }).feed (responseHead ++ body)).error == some .entityTooLarge
