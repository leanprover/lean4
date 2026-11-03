import Std.Http

open Std Http Protocol

/-!
Queries of the HTTP/1.1 machine that the server's connection loop relies on: whether the reader is
idle or reading a head, whether it ran out of input, the body chunks its input already holds, and
the bytes of an error response sent on the machine's behalf.
-/

abbrev M := H1.Machine .receiving

def fresh : M := { config := {} }

/-- Feeds `s`, then runs one step. -/
def feedStep (m : M) (s : String) : M := (m.feed s.toUTF8).step.1

def get : String := "GET / HTTP/1.1\x0d\nHost: x\x0d\n\x0d\n"

def post (extra body : String) : String :=
  s!"POST / HTTP/1.1\x0d\nHost: x\x0d\n{extra}\x0d\n{body}"

def chunked (body : String) : String := post "Transfer-Encoding: chunked\x0d\n" body

-- Idle until a byte of the next request arrives, and reading the head until it is complete.
#guard fresh.isReaderIdle && fresh.isReaderReadingHead
#guard !(fresh.feed "G".toUTF8).isReaderIdle
#guard (feedStep fresh "GET / HTTP/1.1\x0d\nHo").isReaderReadingHead
#guard !(feedStep fresh get).isReaderReadingHead

-- Running out of input is kept until input arrives or ends.
#guard fresh.needsInput == none
#guard fresh.step.1.needsInput == some none
#guard (feedStep fresh "GET / HTTP/1.1\x0d\nHo").needsInput == some none
#guard ((feedStep fresh "GET / HTTP/1.1\x0d\nHo").feed "s".toUTF8).needsInput == none
#guard (feedStep fresh "GET / HTTP/1.1\x0d\nHo").noMoreInput.needsInput == none

-- A fixed-length body that ran out expects the rest of its bytes.
#guard
  let m := feedStep fresh (post "Content-Length: 10\x0d\n" "hello")
  let (m, first) := m.pullBody
  let (m, second) := m.pullBody
  first.isSome && second.isNone && m.needsInput == some (some 5)

-- The whole body is in the input.
#guard
  let (m, chunks) := (feedStep fresh (post "Content-Length: 5\x0d\n" "hello")).pullBuffered 65536
  chunks.map (fun c => (c.chunk.data.size, c.final)) == #[(5, true)] && !m.failed

-- Part of the body: its bytes are pulled, and the pull that finds no more is undone, so the machine
-- neither stalls nor asks for input.
#guard
  let (m, chunks) := (feedStep fresh (post "Content-Length: 10\x0d\n" "hello")).pullBuffered 65536
  chunks.map (fun c => (c.chunk.data.size, c.final)) == #[(5, false)] &&
    m.canPullBodyNow && m.needsInput.isNone

-- A chunk over the body limit is left for a later pull, which fails the message.
#guard
  let m : M := { config := { maxBodySize := 8 } }
  let m := feedStep m (chunked "5\x0d\nhello\x0d\n5\x0d\nworld\x0d\n0\x0d\n\x0d\n")
  let (m, chunks) := m.pullBuffered 65536
  chunks.size == 1 && !m.failed && m.pullBody.1.failed

-- Pulling stops at the chunk that reaches `maxBytes`.
#guard
  let m := feedStep fresh (chunked "5\x0d\naaaaa\x0d\n5\x0d\nbbbbb\x0d\n5\x0d\nccccc\x0d\n0\x0d\n\x0d\n")
  (m.pullBuffered 6).2.size == 2

-- Nothing can be pulled while the client waits for `100 Continue`.
#guard
  let m := feedStep fresh (post "Content-Length: 5\x0d\nExpect: 100-continue\x0d\n" "")
  (m.pullBuffered 65536).2.isEmpty

/-- The error response as the server's connection used to build it, by editing the writer state. -/
def handBuilt (status : Status) : ByteArray :=
  let m := { fresh with writer := { fresh.writer with state := .waitingHeaders } }
  ((m.closeWithError status).step).2.output.toByteArray

#guard [Status.serviceUnavailable, .requestTimeout, .internalServerError].all fun status =>
  (H1.Machine.errorResponse {} status).toByteArray == handBuilt status
#guard (String.fromUTF8! (H1.Machine.errorResponse {} .serviceUnavailable).toByteArray).startsWith
  "HTTP/1.1 503 Service Unavailable\x0d\n"

-- The request's body and the response's framing.
#guard (feedStep fresh get).hasEmptyBody
#guard !(feedStep fresh (post "Content-Length: 5\x0d\n" "hello")).hasEmptyBody
#guard
  let m := feedStep fresh get
  let sent := (m.setKnownSize (.fixed 2)).send ({ status := .ok } : Response.Head)
  !m.isSendingMessage && !m.hasFixedLengthOutput &&
    sent.isSendingMessage && sent.hasFixedLengthOutput && !sent.omitsBody
#guard ((feedStep fresh "HEAD / HTTP/1.1\x0d\nHost: x\x0d\n\x0d\n").send
  ({ status := .ok } : Response.Head)).omitsBody
