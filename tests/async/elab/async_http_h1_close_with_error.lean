import Std.Http

open Std Http
open Std.Http.Protocol.H1

/-!
Tests that `Machine.closeWithError` during a streamed response halts the server machine when input it
has not read follows the request, such as a pipelined request or a stray CRLF. A machine that never
halts keeps the server's connection loop spinning, and the connection never closes. Also tests that
the error response replaces a response whose head was given but not yet written.
-/

/-- Steps `machine` until it halts; `none` if it has not halted after 16 steps. -/
def stepsToHalt (machine : Machine .receiving) : Option Nat := Id.run do
  let mut machine := machine
  for i in [0:16] do
    if machine.halted then return some i
    machine := machine.step.1
  return none

/-- A server machine that has read `input` and is streaming a response to its first request. -/
def streaming (input : String) : Machine .receiving :=
  let machine := (({ config := {} } : Machine .receiving).feed input.toUTF8).step.1
  (machine.send { status := .ok } |>.sendData #[Chunk.ofByteArray "hello".toUTF8]).step.1

def get : String := "GET / HTTP/1.1\r\nHost: a\r\n\r\n"

#eval show IO Unit from do
  for (name, input) in [
      ("nothing after the request", get),
      ("pipelined request", get ++ "GET /2 HTTP/1.1\r\nHost: a\r\n\r\n"),
      ("stray CRLF", get ++ "\r\n"),
      ("unread body, then a pipelined request",
        "POST / HTTP/1.1\r\nHost: a\r\nContent-Length: 3\r\n\r\nabc" ++ get)] do
    for status in [Status.serviceUnavailable, .requestTimeout] do
      if (stepsToHalt ((streaming input).closeWithError status)).isNone then
        throw <| IO.userError
          s!"'{name}', {status.toCode}: the machine did not halt after closeWithError"

-- A response head given but not yet written, waiting for its body, is replaced by the error.
#guard
  let machine := (({ config := {} } : Machine .receiving).feed get.toUTF8).step.1
  let (machine, result) := ((machine.send { status := .ok }).closeWithError .internalServerError).step
  let out := String.fromUTF8! result.output.toByteArray
  out.startsWith "HTTP/1.1 500 Internal Server Error\r\n" && (out.splitOn "200 OK").length == 1 &&
    (stepsToHalt machine).isSome
