module

import Std.Http

/-!
Tests that the HTTP/1.1 machine reports an outgoing body that ends short of its `Content-Length` in
the step that writes its last bytes. A connection loop steps the machine again only on an external
event, so a shortfall left for a later step can go unreported until a timeout.
-/

open Std Http Protocol H1

/-- Steps `machine` until a step writes `needle`, and reports whether that step also closed. -/
private def closesWhenWriting (machine : Machine dir) (needle : String) : IO Bool := do
  let mut machine := machine
  for _ in [0:8] do
    let (next, step) := machine.step
    machine := next
    let wrote := String.fromUTF8! (step.output.data.foldl (· ++ ·) .empty)
    if wrote.contains needle then
      return step.events.any (· matches .close) && machine.error == some .badMessage
  throw <| IO.userError s!"{needle.quote} was never written"

/-- A request head that declares a 10-byte body. -/
private def putHead : Request.Head :=
  (Request.new |>.method .put |>.uri! "/upload" |>.header! "Host" "example.com"
    |>.header! "Content-Length" "10").line

-- Client side: the request body ends after 5 of its 10 declared bytes.
#eval show IO Unit from do
  let machine : Machine .sending := { config := {} }
  let machine := machine.send putHead
    |>.sendData #[Chunk.ofByteArray "12345".toUTF8] |>.userClosedBody
  unless ← closesWhenWriting machine "12345" do
    throw <| IO.userError "a request body 5 bytes short was not reported in the step that wrote it"

-- Control: the whole declared body completes the message without an error.
#eval show IO Unit from do
  let machine : Machine .sending := { config := {} }
  let mut machine := machine.send putHead
    |>.sendData #[Chunk.ofByteArray "0123456789".toUTF8] |>.userClosedBody
  for _ in [0:8] do
    let (next, _) := machine.step
    machine := next
  if machine.error.isSome then
    throw <| IO.userError s!"a complete body failed with {machine.error.map toString}"
