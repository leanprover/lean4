import Std.Http

open Std Http Server

/-!
Tests `Server.Driver`, the decisions of an HTTP/1.1 server connection, by stepping it with inputs and
reading the commands it returns, with no I/O: a request answered and its connection kept alive, the
timeouts of an idle connection and of a partial head, a shutdown while a handler runs, a failed write,
a rejected `Expect: 100-continue`, an exchange ended early being reported once, and the 500 that
replaces a 1xx final response.
-/

def cfg : Http.Config := { generateDate := false }

/-- The bytes of the write commands in `cmds`. -/
def written (cmds : Array Driver.Command) : String :=
  String.fromUTF8! <| cmds.foldl (init := .empty) fun acc cmd =>
    match cmd with
    | .write data => acc ++ data.toByteArray
    | _ => acc

def reports (cmds : Array Driver.Command) : Array String :=
  cmds.filterMap fun | .report err => some (toString err) | _ => none

/-- Steps the driver through `inputs` at time `now`, answering each write batch with `written true`,
and returns the final state with every command. -/
def drive (s : Driver.State) (inputs : List Driver.Input) (now : Nat := 0) :
    Driver.State × Array Driver.Command := Id.run do
  let mut s := s
  let mut all := #[]
  let mut pending := inputs
  let mut input := Driver.Input.resume
  let mut started := false
  for _ in [0:64] do
    if started then
      match pending with
      | [] => break
      | i :: rest =>
        input := i
        pending := rest
    started := true
    -- Answer write batches and passes until the driver waits for an outside input.
    for _ in [0:16] do
      let (s', cmds) := Driver.step cfg s now input
      s := s'
      all := all ++ cmds
      if cmds.any (· matches .write _ | .awaitWritten | .flush) then
        input := .written true
      else if s.waits || s.isClosed then
        break
      else
        input := .resume
  return (s, all)

def fresh : Driver.State := Driver.init { config := cfg.toH1Config }

def getRequest : ByteArray := "GET / HTTP/1.1\r\nHost: a\r\n\r\n".toUTF8

def okHead : Response.Head := { status := .ok }

/-! ## A request answered on a kept-alive connection -/

-- A new connection polls the socket under the keep-alive timer.
#guard
  let (s, _) := drive fresh []
  let src := Driver.sources cfg s false false
  s.waits && src.recv == some cfg.defaultPayloadBytes && src.timer matches some (.afterWrites _)

-- A complete GET starts its handler and waits for the response, untimed.
#guard
  let (s, cmds) := drive fresh [.received (some getRequest)]
  let src := Driver.sources cfg s false false
  cmds.any (· matches .startHandler _) && src.response && src.timer.isNone

-- The response goes out, the exchange ends, and the connection waits for the next request.
#guard
  let (s, cmds) := drive fresh
    [.received (some getRequest), .responded okHead (some (.fixed 2)) (.ok (some (some (Chunk.ofByteArray "ok".toUTF8)))),
     .pulled none]
  let out := written cmds
  out.startsWith "HTTP/1.1 200 OK\r\n" && out.endsWith "\r\n\r\nok" &&
    cmds.any (· matches .nextExchange) && s.waits &&
    (Driver.sources cfg s false false).timer matches some (.afterWrites _)

/-! ## Timeouts -/

-- An idle connection closes quietly when its timer passes: no response, no report, no lingering.
#guard
  let (s, cmds) := drive fresh [.cancelled true false]
  s.isClosed && written cmds == "" && reports cmds == #[] && cmds.any (· matches .close false)

-- A partial head whose timer passes is reported and the connection closes. The machine answers only
-- a complete head, so no 408 goes out.
#guard
  let (s, cmds) := drive fresh [.received (some "GET / HTTP/1.1\r\nHo".toUTF8), .cancelled true false]
  s.isClosed && written cmds == "" && reports cmds == #["request header timeout"]

-- The first byte after idle starts the header timer from the time it arrived.
#guard
  let (s, _) := drive fresh [.received (some "G".toUTF8)] (now := 1000)
  s.timer matches .header 6000

/-! ## Shutdown and write failures -/

-- A shutdown while a handler runs answers 503, and the handler's response is no longer waited for.
#guard
  let (s, cmds) := drive fresh [.received (some getRequest), .cancelled false false]
  (written cmds).startsWith "HTTP/1.1 503 Service Unavailable\r\n" && s.isClosed &&
    !s.handlerRunning

-- A failed write ends the connection without lingering.
#guard
  let (s, cmds) := drive fresh []
  let (s, more) := Driver.step cfg s 0 (.received (some getRequest))
  let (s, more') := Driver.step cfg s 0 (.written false)
  let (s, last) := Driver.step cfg s 0 (.written false)
  (cmds ++ more ++ more').any (· matches .flush) && s.isClosed && last.any (· matches .close false)

/-! ## `Expect: 100-continue` -/

-- An unsafe request waits for earlier writes before asking; a rejection answers 417 and never runs
-- the handler.
#guard
  let req := "POST / HTTP/1.1\r\nHost: a\r\nContent-Length: 3\r\nExpect: 100-continue\r\n\r\n".toUTF8
  let (s, cmds) := drive fresh [.received (some req)]
  let asked := s.asksContinue && cmds.any (· matches .awaitWritten) && cmds.any (· matches .askContinue _)
  let (_, cmds') := drive s [.continueDecided false]
  asked && (written cmds').startsWith "HTTP/1.1 417 Expectation Failed\r\n" &&
    !(cmds ++ cmds').any (· matches .startHandler _)

/-! ## An exchange ended early is reported once -/

def postPartial : ByteArray := "POST / HTTP/1.1\r\nHost: a\r\nContent-Length: 10\r\n\r\nabc".toUTF8

def bodyEnds (cmds : Array Driver.Command) : Array String :=
  cmds.filterMap fun | .endBody r => some r | _ => none

-- A handler that ends the exchange with a 1xx gets a 500 and one report, though the rest of the
-- request body never arrives.
#guard
  let (s, cmds) := drive fresh [.received (some postPartial), .responded { status := .«continue» } none (.ok none)]
  s.isClosed && (written cmds).startsWith "HTTP/1.1 500 Internal Server Error\r\n" &&
    reports cmds == #["Other error: the final response has the interim status 100"] &&
    cmds.any (· matches .close true)

-- The 500 that replaces a 1xx final response to `HEAD` keeps its `Content-Length` but carries no
-- content (RFC 9110 §9.3.2).
#guard
  let headRequest := "HEAD / HTTP/1.1\r\nHost: a\r\n\r\n".toUTF8
  let (s, cmds) := drive fresh [.received (some headRequest), .responded { status := .earlyHints } none (.ok none)]
  let out := written cmds
  s.isClosed && out.startsWith "HTTP/1.1 500 Internal Server Error\r\n" &&
    out.endsWith "Content-Length: 22\r\n\r\n" &&
    reports cmds == #["Other error: the final response has the interim status 103"]

-- A timeout or a failed handler while the request body is incomplete is reported once, and the body
-- ends because the connection closes, not because of a failure of its own.
#guard
  [Driver.Input.cancelled true false, .handlerFailed (.userError "boom")].all fun abort =>
    let (s, cmds) := drive fresh [.received (some postPartial), .bodyInterest true, abort]
    s.isClosed && (reports cmds).size == 1 &&
      bodyEnds cmds == #["the connection closed before the request body was complete"] &&
      cmds.any (· matches .close true)

/-! ## A closed connection -/

#guard
  let (s, _) := drive fresh [.cancelled true false]
  let (s', cmds) := Driver.step cfg s 0 (.received (some getRequest))
  s'.isClosed && cmds.isEmpty

/-! ## The `Date` header -/

-- The driver formats `Date` from the wall clock it is given, once per second.
#guard
  let dated : Http.Config := { generateDate := true }
  let at0 := Std.Time.Timestamp.ofMillisecondsSinceUnixEpoch 1_700_000_000_000
  let at1 := Std.Time.Timestamp.ofMillisecondsSinceUnixEpoch 1_700_000_000_900
  let at2 := Std.Time.Timestamp.ofMillisecondsSinceUnixEpoch 1_700_000_001_000
  let date (s : Driver.State) := s.machine.date.map (·.value)
  let (s, _) := Driver.step dated fresh 0 .resume (some at0)
  let (s1, _) := Driver.step dated { s with machine := { s.machine with date := none } } 0 (.written true) (some at1)
  let (s2, _) := Driver.step dated s1 0 (.received none) (some at2)
  date s == some "Tue, 14 Nov 2023 22:13:20 GMT" && date s1 == none &&
    date s2 == some "Tue, 14 Nov 2023 22:13:21 GMT"

-- Without `generateDate`, no `Date` is set.
#guard (Driver.step cfg fresh 0 .resume (some (Std.Time.Timestamp.ofMillisecondsSinceUnixEpoch 0))).1.machine.date.isNone
