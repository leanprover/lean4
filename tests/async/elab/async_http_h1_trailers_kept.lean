import Std.Http

open Std Http
open Std.Http.Protocol.H1

/-!
Tests that the HTTP/1.1 machine keeps the trailer fields of an incoming chunked message for its
user (`Machine.takeTrailers`): the fields in order, none for a message without them, without the
fields a trailer may not carry (RFC 9110 §6.5.1), and afresh for each message on a connection.
-/

def request : Request.Head :=
  { method := .get, version := .v11, uri := RequestTarget.parse! "/",
    headers := Headers.empty.insert .host (.mk "a") }

/-- Steps `machine` `n` times. -/
def steps (machine : Machine .sending) (n : Nat := 8) : Machine .sending := Id.run do
  let mut machine := machine
  for _ in [0:n] do
    machine := machine.step.1
  return machine

/-- Pulls the body to its end, returning the machine and the bytes read. -/
def pullAll (machine : Machine .sending) (fuel : Nat := 16) : Machine .sending × String := Id.run do
  let mut machine := machine
  let mut body := ""
  for _ in [0:fuel] do
    let (next, pulled) := steps machine |>.pullBody
    machine := next
    match pulled with
    | some chunk =>
      body := body ++ String.fromUTF8! chunk.chunk.data
      if chunk.final then return (machine, body)
    | none => pure ()
  return (machine, body)

/-- A client machine that sent a GET, then read `response` and its body to the end. -/
def read (response : String) (machine : Machine .sending := { config := {} }) :
    Machine .sending × String :=
  pullAll (steps ((steps (machine.send request |>.userClosedBody)).feed response.toUTF8))

def trailersOf (response : String) : String × Array (String × String) :=
  let (machine, body) := read response
  (body, machine.takeTrailers.2)

-- The fields of the trailer section, in order.
#guard trailersOf
    "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n2\r\nab\r\n0\r\nX-A: 1\r\nX-B: 2\r\n\r\n" ==
  ("ab", #[("X-A", "1"), ("X-B", "2")])

-- None for a message without a trailer section.
#guard trailersOf "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n2\r\nab\r\n0\r\n\r\n" == ("ab", #[])

-- Fields that framing, routing, authentication or the response's controls depend on may not be sent
-- in a trailer (RFC 9110 §6.5.1): they are dropped.
#guard trailersOf
    "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n0\r\nContent-Length: 5\r\nX-A: 1\r\nHost: b\r\n\r\n" ==
  ("", #[("X-A", "1")])

-- Taking them leaves none.
#guard
  let (machine, _) := read "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n0\r\nX-A: 1\r\n\r\n"
  machine.takeTrailers.1.takeTrailers.2 == #[]

-- The next message on the connection starts with none.
#guard
  let (machine, _) := read "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n0\r\nX-A: 1\r\n\r\n"
  let (machine, _) := read "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n0\r\n\r\n" machine
  machine.takeTrailers.2 == #[]
