import Std.Http
import Std.Http.Test.Helpers

open Std.Async
open Std Http
open Std.Http.Internal
open Std.Http.Internal.Test

/-!
Tests that a request body keeps arriving after a reader withdraws from a select. A
`Body.Stream.recvSelector` registered by `Selectable.one` asks the connection for the body, and
another case can win the select before any body byte arrives. The connection has then pulled, found
nothing, and waits for more input: it must keep reading the socket, so that the next read gets the
whole body instead of nothing.
-/

/--
Never ready when polled, and wins the select as soon as it is registered, like an event that fires
while `Selectable.one` registers its other cases.
-/
def winsOnRegister : Selector Unit where
  tryFn := pure none
  registerFn waiter := waiter.race (pure ()) fun promise => promise.resolve (.ok ())
  unregisterFn := pure ()

/-- Receives every chunk of `body`, or stops once no chunk arrives for `ms` milliseconds. -/
partial def recvUntilIdle (body : Body.Stream) (ms : Std.Time.Millisecond.Offset) (acc : ByteArray := .empty) :
    Async (ByteArray × Bool) := do
  let next ← Selectable.one #[
    .case body.recvSelector (fun c => pure (some c)),
    .case (← Selector.sleep ms) (fun _ => pure none)]
  match next with
  | some (some chunk) => recvUntilIdle body ms (acc ++ chunk.data)
  | some none => return (acc, true)
  | none => return (acc, false)

/--
Selects on the body against `winsOnRegister` until `withdrawn` is resolved, losing every select, then
answers with the body it reads. `Selectable.one` registers its cases in random order, so some of
these selects register `recvSelector` before `winsOnRegister` ends them.
-/
def withdrawingHandler (withdrawn : IO.Promise Unit) : TestHandler := fun req => do
  for _ in [0:16] do
    let got ← (Selectable.one #[
      .case req.body.recvSelector (fun _ => pure true),
      .case winsOnRegister (fun _ => pure false)] : Async Bool)
    if got then
      return ← Response.badRequest |>.text "a body chunk arrived before the client sent it"
    -- Gives the connection time to act on the interest the select showed.
    (sleep 5 : Async Unit)
  withdrawn.resolve ()
  let (bytes, ended) ← (recvUntilIdle req.body 2000 : Async _)
  if ended then
    Response.ok |>.text (String.fromUTF8! bytes)
  else
    Response.internalServerError |>.text s!"the body stopped arriving after {bytes.size} bytes"

/--
Sends `head`, waits until the handler has withdrawn from its selects, then sends `body` in `pieces`
and returns everything the server wrote.
-/
def exchange (head body : String) (pieces : Nat) : IO String := do
  let (client, server) ← Mock.new
  let withdrawn ← IO.Promise.new
  Async.block do
    client.send head.toUTF8
    let serving ← async (t := AsyncTask)
      (Std.Http.Server.serveConnection server (withdrawingHandler withdrawn) defaultConfig |>.run)
    let some () ← await withdrawn.result? | throw (IO.userError "the handler never withdrew")
    let bytes := body.toUTF8
    let size := (bytes.size + pieces - 1) / pieces
    for i in [0:pieces] do
      client.send (bytes.extract (i * size) ((i + 1) * size))
    await serving
    let mut out := ByteArray.empty
    repeat
      match ← client.tryRecv? with
      | some b => out := out ++ b
      | none => break
    return String.fromUTF8! out

def content : String := String.join (List.replicate 40 "0123456789")

def expectWholeBody (name head body : String) (pieces : Nat) : IO Unit := do
  let out ← exchange head body pieces
  unless out.startsWith "HTTP/1.1 200" && out.endsWith ("\r\n\r\n" ++ content) do
    throw (IO.userError s!"{name}, body sent in {pieces} pieces: expected 200 with the whole body, got {out.quote}")

def fixedHead : String :=
  s!"POST / HTTP/1.1\r\nHost: example.com\r\nConnection: close\r\nContent-Length: {content.length}\r\n\r\n"

def chunkedHead : String :=
  "POST / HTTP/1.1\r\nHost: example.com\r\nConnection: close\r\nTransfer-Encoding: chunked\r\n\r\n"

def chunkedBody : String :=
  s!"{String.ofList (Nat.toDigits 16 content.length)}\r\n{content}\r\n0\r\n\r\n"

#eval expectWholeBody "Content-Length body" fixedHead content 1
#eval expectWholeBody "Content-Length body" fixedHead content 8
#eval expectWholeBody "chunked body" chunkedHead chunkedBody 1
#eval expectWholeBody "chunked body" chunkedHead chunkedBody 8
