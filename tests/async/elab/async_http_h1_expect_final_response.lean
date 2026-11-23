import Std.Http

open Std Http
open Std.Http.Protocol.H1

/-!
Tests a server machine whose final response is written while it still waits for the
`Expect: 100-continue` decision. The request body will never be read, so the machine closes the
connection and halts; a later `canContinue` writes nothing after the final response.
-/

def request : String :=
  "POST / HTTP/1.1\r\nHost: a\r\nExpect: 100-continue\r\nContent-Length: 5\r\n\r\n"

/-- Steps `machine` until it halts. Returns its output, or `none` if it has not halted after 16 steps. -/
def runToHalt (machine : Machine .receiving) : Option String := Id.run do
  let mut machine := machine
  let mut out := ""
  for _ in [0:16] do
    let (next, step) := machine.step
    machine := next
    out := out ++ String.fromUTF8! step.output.toByteArray
    if machine.halted then return some out
  return none

#eval show IO Unit from do
  let machine := (({ config := {} } : Machine .receiving).feed request.toUTF8).step.1
  let answered := machine.setKnownSize (.fixed 2) |>.send { status := .ok }
    |>.sendData #[Chunk.ofByteArray "ok".toUTF8] |>.userClosedBody
  let some out := runToHalt answered
    | throw <| IO.userError "the machine did not halt after its final response"
  -- RFC 9110 §10.1.1: the response ends the exchange without the body, so it says so.
  unless out == "HTTP/1.1 200 OK\r\nConnection: close\r\nContent-Length: 2\r\n\r\nok" do
    throw <| IO.userError s!"unexpected output {out.quote}"
  -- A `canContinue` after the final response writes nothing more.
  let some out := runToHalt (answered.step.1.canContinue .«continue»)
    | throw <| IO.userError "the machine did not halt after a late canContinue"
  unless out.isEmpty do
    throw <| IO.userError s!"a late canContinue wrote {out.quote}"
