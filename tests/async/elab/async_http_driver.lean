import Std.Http.Server.Driver

open Std Http
open Std.Http.Protocol
open Std.Http.Server
open Std.Http.Server.Driver

/-!
Pure tests of the HTTP/1.1 server connection driver (`Std.Http.Server.Driver`). Scripted inputs drive
`step`, with no socket and no handler. They check that pipelined requests get one response each, in
order; that a truncated request body reaches the handler as an error and never as a clean end; that a
half-closed peer stops the reads; that every timeout fires through `nextDeadline`; the
`Expect: 100-continue` flow; write backpressure and the read-ahead bound; that the connection closes
exactly once; and that inputs from sources that are not armed change nothing.
-/

/-! ## Harness -/

def newMachine (config : Http.Config := { generateDate := false }) : H1.Machine .receiving :=
  { config := config.toH1Config }

structure Run where
  cfg : Http.Config := {}
  state : State
  now : Nat := 0
  /-- Every command so far. -/
  log : Array Command := #[]
  /-- The commands of the last step. -/
  last : Array Command := #[]

def Run.start (cfg : Http.Config := {}) (machine := newMachine) (now := 0) : Run :=
  let (state, cmds) := Driver.start cfg machine now
  { cfg, state, now, log := cmds, last := cmds }

def Run.input (r : Run) (i : Input) : Run :=
  let (state, cmds) := step r.cfg r.state r.now i
  { r with state, log := r.log ++ cmds, last := cmds }

def Run.at (r : Run) (now : Nat) : Run := { r with now }

/-- Whether the connection receives. -/
def Run.receiving (r : Run) : Bool := wantsBytes r.cfg r.state

/-- Whether the connection pulls the response body. -/
def Run.pulling (r : Run) : Bool := pullsResponse r.state

def tag : Command → String
  | .write _ => "write"
  | .startHandler .. => "startHandler"
  | .askContinue _ => "askContinue"
  | .pushBody .. => "pushBody"
  | .failBody _ => "failBody"
  | .releaseResponse => "releaseResponse"
  | .report _ => "report"
  | .abandonHandler => "abandonHandler"
  | .close _ => "close"

def tags (cmds : Array Command) : Array String := cmds.map tag

def count (cmds : Array Command) (t : String) : Nat := (cmds.filter (tag · == t)).size

def has (cmds : Array Command) (t : String) : Bool := cmds.any (tag · == t)

def indexOf (cmds : Array Command) (t : String) : Nat := (cmds.findIdx? (tag · == t)).getD cmds.size

def bytesOf (cmds : Array Command) : String :=
  String.fromUTF8! <| cmds.foldl (init := .empty) fun acc cmd =>
    match cmd with
    | .write data => acc ++ data.toByteArray
    | _ => acc

def started (cmds : Array Command) : Array String :=
  cmds.filterMap fun
    | .startHandler head _ _ => some (toString head.uri)
    | _ => none

/-- Whether each handler started with its body already complete. -/
def completeBodies (cmds : Array Command) : Array Bool :=
  cmds.filterMap fun
    | .startHandler _ _ complete => some complete
    | _ => none

def pushed (cmds : Array Command) : String :=
  String.fromUTF8! <| cmds.foldl (init := .empty) fun acc cmd =>
    match cmd with
    | .pushBody chunk _ _ => acc ++ chunk.data
    | _ => acc

/-- How many request bodies were ended cleanly. -/
def ended (cmds : Array Command) : Nat :=
  (cmds.filter fun | .pushBody _ _ final => final | _ => false).size

def reports (cmds : Array Command) : Array String :=
  cmds.filterMap fun
    | .report err => some (toString err)
    | _ => none

def lingered (cmds : Array Command) : Bool :=
  cmds.any fun | .close linger => linger | _ => false

def check (cond : Bool) (msg : String) : IO Unit :=
  unless cond do throw (IO.userError msg)

def checkTags (r : Run) (expected : Array String) (what : String) : IO Unit :=
  check (tags r.last == expected) s!"{what}: expected {expected}, got {tags r.last}"

/--
The connection closed exactly once, last, and every request body handed to a handler ended exactly
once: cleanly or with an error.
-/
def checkCleanup (r : Run) (what : String) : IO Unit := do
  check r.state.isClosed s!"{what}: not closed ({tags r.log})"
  check (count r.log "close" == 1) s!"{what}: closed {count r.log "close"} times"
  check (r.log.back?.any (tag · == "close")) s!"{what}: close is not the last command"
  let ends := ended r.log + count r.log "failBody"
  let openBodies := (completeBodies r.log).filter (!·) |>.size
  check (ends == openBodies) s!"{what}: {openBodies} open bodies, {ends} ends ({tags r.log})"
  -- After closing, nothing happens any more.
  for i in [Input.resume, .received none, .written, .bodyInterest true, .pulled none,
      .cancelled false, .deadline .idle, .received (some "GET / HTTP/1.1\r\n\r\n".toUTF8),
      .continueDecided true] do
    check (step r.cfg r.state (r.now + 100000) i).2.isEmpty s!"{what}: a closed connection acted"
  check (nextDeadline r.state).isNone s!"{what}: a closed connection keeps a deadline"

def req (s : String) : Input := .received (some s.toUTF8)

def full (body : String) : Input :=
  .responded {} (some (.fixed body.utf8ByteSize)) #[{ data := body.toUTF8 }] true

def streamed : Input := .responded {} none #[] false

def chunk (s : String) : Input := .pulled (some { data := s.toUTF8 })

def get (path : String) (extra := "") : String :=
  s!"GET {path} HTTP/1.1\r\nHost: x\r\n{extra}\r\n"

def post (path : String) (body : String) (extra := "") : String :=
  s!"POST {path} HTTP/1.1\r\nHost: x\r\nContent-Length: {body.utf8ByteSize}\r\n{extra}\r\n{body}"

/-- A request head stating a body of `declared` bytes, followed by the first bytes `sent` of it. -/
def postPart (path : String) (declared : Nat) (sent : String) : String :=
  s!"POST {path} HTTP/1.1\r\nHost: x\r\nContent-Length: {declared}\r\n\r\n{sent}"

/-! ## One response per request, in order -/

#eval show IO Unit from do
  let r := Run.start
  check (r.receiving && r.last.isEmpty) "a new connection receives"
  let r := r.input (req (get "/a" ++ get "/b"))
  check (started r.last == #["/a"]) s!"only /a starts: {tags r.last}"
  let r := r.input (full "A")
  check (started r.last == #["/b"]) s!"/b starts once /a is answered: {tags r.last}"
  check (has r.last "write") "the answer to /a is written"
  check (indexOf r.last "write" < indexOf r.last "startHandler") "the answer to /a is written first"
  check (!r.receiving) "no read while a pipelined handler runs"
  let r := r.input .written
  let r := r.input (full "B")
  check (count r.log "startHandler" == 2) "two handlers"
  let out := bytesOf r.log
  check ((out.splitOn "HTTP/1.1 200 OK").length == 3) s!"two responses: {out.quote}"
  match out.splitOn "\r\n\r\nA" with
  | [_, rest] => check (rest.contains "\r\n\r\nB") s!"B after A: {out.quote}"
  | _ => check false s!"one A: {out.quote}"
  check r.receiving "the connection waits for the next request"

-- A pipelined request with an unsafe method waits until the earlier response is written.
#eval show IO Unit from do
  let r := Run.start
  let r := r.input (req (get "/a" ++ post "/b" ""))
  let r := r.input (full "A")
  check (started r.last == #[]) s!"POST waits for the write: {tags r.last}"
  let r := r.input .written
  check (started r.last == #["/b"]) s!"POST starts once written: {tags r.last}"

-- Three pipelined requests, with bodies, answered in order; then the connection closes.
#eval show IO Unit from do
  let r := Run.start
  let r := r.input (req (post "/1" "aa" ++ post "/2" "bbb" ++ get "/3" "Connection: close\r\n"))
  check (started r.last == #["/1"]) "first"
  let r := r.input (.bodyInterest true)
  check (pushed r.last == "aa" && ended r.last == 1) s!"the first body: {tags r.last}"
  let r := r.input (full "one")
  check (started r.last == #[]) s!"an unsafe request waits for the write: {tags r.last}"
  let r := r.input .written
  check (started r.last == #["/2"]) s!"second: {tags r.log}"
  let r := r.input (.bodyInterest true)
  check (pushed r.last == "bbb" && ended r.last == 1) s!"the second body: {tags r.last}"
  let r := r.input (full "two")
  check (started r.last == #["/3"]) "a safe request starts before the earlier response is confirmed"
  let r := r.input .written
  let r := r.input (full "three")
  check (!r.receiving) "no read after Connection: close"
  let r := r.input .written
  check (!lingered r.log) "nothing to linger for"
  checkCleanup r "pipeline"
  let out := bytesOf r.log
  check ((out.splitOn "HTTP/1.1 200 OK").length == 4) s!"three responses: {out.quote}"

/-! ## A truncated body is an error, never a clean end -/

#eval show IO Unit from do
  let r := Run.start
  let r := r.input (req (postPart "/u" 10 "abc"))
  check (completeBodies r.last == #[false]) s!"one handler, body incomplete: {tags r.last}"
  check (wantsBodyInterest r.state) "the reader is watched"
  check (!r.receiving) "no read until the reader wants more"
  let r := r.input (.bodyInterest true)
  check (pushed r.last == "abc" && ended r.last == 0) s!"abc pushed: {tags r.last}"
  check (wantsBodyInterest r.state && !r.receiving) "watched again, no read yet"
  let r := r.input (.bodyInterest true)
  check r.receiving "the reader waits: receive"
  let r := r.input (.received none)
  check (count r.log "failBody" == 1) s!"the body fails: {tags r.log}"
  check (ended r.log == 0) "the body never ends cleanly"
  check (reports r.log == #["Connection closed"]) s!"reported: {reports r.log}"
  let r := r.input .written
  check (!lingered r.log) "the peer closed: nothing to linger for"
  checkCleanup r "truncated body"

-- A chunked body cut inside a chunk: the piece that arrived is handed over, then the body fails.
#eval show IO Unit from do
  let r := Run.start
  let r := r.input (req "POST /c HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nab")
  check (completeBodies r.last == #[false]) "incomplete"
  let r := r.input (.bodyInterest true)
  check (pushed r.last == "ab") s!"ab pushed: {tags r.last}"
  check r.receiving "the rest of the chunk is received"
  let r := r.input (.received none)
  check (count r.log "failBody" == 1 && ended r.log == 0) s!"fails: {tags r.log}"

-- A complete body ends cleanly.
#eval show IO Unit from do
  let r := Run.start
  let r := r.input (req (post "/ok" "abc"))
  let r := r.input (.bodyInterest true)
  check (pushed r.last == "abc" && ended r.last == 1) s!"pushed and ended: {tags r.last}"
  let r := r.input (full "ok")
  check (count r.log "failBody" == 0) "no failure"

-- A request without a body starts its handler with the body closed.
#eval show IO Unit from do
  let r := Run.start |>.input (req (get "/"))
  check (completeBodies r.last == #[true]) s!"complete: {tags r.last}"
  check (!wantsBodyInterest r.state) "nothing to watch"

-- A response written in full before the body was read cuts the body with an error, and the rest of
-- the body is drained.
#eval show IO Unit from do
  let r := Run.start
  let r := r.input (req (postPart "/early" 10 "abcde"))
  let r := r.input (full "early")
  check (count r.last "failBody" == 1) s!"cut: {tags r.last}"
  check (r.last.any fun
      | .failBody err => toString err == "the request body was discarded after the response was written"
      | _ => false)
    "says why"
  check r.receiving "the rest of the body is drained"
  let r := r.input .written |>.input (req "fghij")
  check (r.receiving && r.state.machine.reader.messageCount == 1) "next exchange"

/-! ## A half-closed peer stops the reads -/

#eval show IO Unit from do
  let r := Run.start
  let r := r.input (req (get "/s"))
  let r := r.input streamed
  check r.pulling "pull the body"
  check r.receiving "read ahead while the response is under way"
  let r := r.input (chunk "one")
  check (has r.last "write" && r.pulling) "written, pull again"
  let r := r.input (.received none)
  check (!r.receiving) "no read after EOF"
  let mut r := r
  for i in [0:5] do
    r := r.input (chunk s!"part {i}")
    check r.pulling "keeps streaming"
    check (!r.receiving) "no read after EOF"
    r := r.input .written
  r := r.input (.received none)
  check (r.last.isEmpty) "a second EOF is ignored"
  r := r.input (.pulled none)
  r := r.input .written
  check ((bytesOf r.log).endsWith "0\r\n\r\n") "the response completes"
  checkCleanup r "half-close"

-- Read-ahead stops at `readAhead` unread bytes.
#eval show IO Unit from do
  let r := Run.start { maximumRecvSize := 16 }
  let r := r.input (req (get "/s"))
  let r := r.input streamed
  check r.receiving "reads ahead"
  let r := r.input (req (get "/t"))
  check (!r.receiving) s!"stops reading at the bound: {tags r.last}"
  let r := r.input (.pulled none)
  check (started r.last == #["/t"]) "the pipelined request starts after the response"

/-! ## Timeouts fire through `nextDeadline` -/

-- Idle before the first request: closes without a response.
#eval show IO Unit from do
  let r := Run.start
  check (nextDeadline r.state == some (.idle, 12000)) s!"idle deadline: {repr (nextDeadline r.state)}"
  let r := r.at 11999 |>.input (.deadline .idle)
  check r.last.isEmpty "not due yet"
  let r := r.at 12000 |>.input (.deadline .header)
  check r.last.isEmpty "a deadline that does not run is ignored"
  let r := r.input (.deadline .idle)
  check (!has r.last "write" && has r.last "close") s!"idle closes: {tags r.last}"
  checkCleanup r "idle"

-- Idle after a response: counted from when the writes are confirmed; until then the write deadline
-- runs.
#eval show IO Unit from do
  let r := Run.start |>.at 100 |>.input (req (get "/"))
  let r := r.at 200 |>.input (full "A")
  check (nextDeadline r.state == some (.write, 30200)) s!"write deadline: {repr (nextDeadline r.state)}"
  let r := r.at 300 |>.input .written
  check (nextDeadline r.state == some (.idle, 12300)) s!"idle deadline: {repr (nextDeadline r.state)}"

-- A request head that does not complete in time.
#eval show IO Unit from do
  let r := Run.start |>.at 100 |>.input (req "GET / HTTP/1.1\r\nHo")
  check (nextDeadline r.state == some (.header, 5100)) s!"header deadline: {repr (nextDeadline r.state)}"
  let r := r.at 1000 |>.input (req "st: x\r\nA: b")
  check (nextDeadline r.state == some (.header, 5100)) "more bytes keep the deadline"
  let r := r.at 5100 |>.input (.deadline .header)
  check ((reports r.log)[0]? == some "request header timeout") s!"{reports r.log}"
  let r := r.input .written
  checkCleanup r "header timeout"

-- Body bytes that a reader waits for and that do not come: 408, and the body fails.
#eval show IO Unit from do
  let r := Run.start |>.input (req (postPart "/slow" 10 "abc"))
  let r := r.input (.bodyInterest true) |>.at 50 |>.input (.bodyInterest true)
  check (nextDeadline r.state == some (.linger, 10050)) s!"linger deadline: {repr (nextDeadline r.state)}"
  let r := r.at 10050 |>.input (.deadline .linger)
  check ((bytesOf r.last).startsWith "HTTP/1.1 408") s!"408: {(bytesOf r.last).quote}"
  check (count r.log "failBody" == 1 && ended r.log == 0) "the body fails"
  check (has r.last "abandonHandler") "the handler's response is abandoned"
  let r := r.input .written
  check (lingered r.log) "the peer may still send the body: linger"
  checkCleanup r "linger timeout"

-- A response body whose next chunk does not come in time ends the connection.
#eval show IO Unit from do
  let r := Run.start |>.input (req (get "/stall")) |>.input streamed |>.input (chunk "first")
  let r := r.at 10 |>.input .written
  check (nextDeadline r.state == some (.linger, 10010)) s!"linger deadline: {repr (nextDeadline r.state)}"
  let r := r.at 10010 |>.input (.deadline .linger)
  check (reports r.log == #["request header timeout"]) s!"{reports r.log}"
  check (has r.last "releaseResponse") s!"released: {tags r.last}"
  let r := r.input .written
  checkCleanup r "stalled producer"

-- Writes that are never confirmed drop the connection without waiting for them.
#eval show IO Unit from do
  let r := Run.start |>.input (req (get "/"))
  let r := r.input (full "x")
  check (nextDeadline r.state == some (.write, 30000)) s!"{repr (nextDeadline r.state)}"
  let r := r.at 30000 |>.input (.deadline .write)
  check (has r.last "close" && !lingered r.last) s!"dropped: {tags r.last}"
  checkCleanup r "write timeout"

-- While a response streams, a write that is not confirmed drops it too; its body is released.
#eval show IO Unit from do
  let r := Run.start |>.input (req (get "/")) |>.input streamed |>.input (chunk "x")
  let r := r.at 10000 |>.input (.deadline .linger)
  check (has r.last "releaseResponse") s!"released: {tags r.last}"
  check (r.state.phase == .draining) "draining"
  check (nextDeadline r.state == some (.write, 30000)) s!"the flush is bounded: {repr (nextDeadline r.state)}"
  let r := r.at 30000 |>.input (.deadline .write)
  check (has r.last "close") s!"dropped: {tags r.last}"
  checkCleanup r "write timeout while streaming"

-- The final flush is bounded by the write deadline too.
#eval show IO Unit from do
  let r := Run.start |>.input (req (get "/" "Connection: close\r\n"))
  let r := r.at 10 |>.input (full "bye")
  check (r.state.phase == .draining) "draining"
  check (nextDeadline r.state == some (.write, 30010)) s!"{repr (nextDeadline r.state)}"
  let r := r.at 30010 |>.input (.deadline .write)
  check (has r.last "close") s!"closed: {tags r.last}"
  checkCleanup r "flush timeout"

/-! ## Expect: 100-continue -/

def expectPost : String :=
  "POST /e HTTP/1.1\r\nHost: x\r\nContent-Length: 3\r\nExpect: 100-continue\r\n\r\n"

#eval show IO Unit from do
  let r := Run.start |>.input (req expectPost)
  checkTags r #["askContinue"] "ask first"
  check (!r.receiving) "read nothing before the decision"
  let r := r.input (.continueDecided true)
  check ((bytesOf r.last).startsWith "HTTP/1.1 100 Continue\r\n") s!"100: {(bytesOf r.last).quote}"
  check (has r.last "startHandler") s!"the handler starts with the 100: {tags r.last}"
  check (indexOf r.last "write" < indexOf r.last "startHandler") "100 before the handler"
  let r := r.input (.bodyInterest true)
  check r.receiving "the body is read after the 100"
  let r := r.input (req "abc")
  check (pushed r.last == "abc" && ended r.last == 1) s!"the body arrives: {tags r.last}"

#eval show IO Unit from do
  let r := Run.start |>.input (req expectPost)
  let r := r.input (.continueDecided false)
  check ((bytesOf r.last).startsWith "HTTP/1.1 417") s!"417: {(bytesOf r.last).quote}"
  check (count r.log "startHandler" == 0) "the handler never runs"
  let r := r.input .written
  checkCleanup r "expect rejected"

-- The decision has a deadline, and a late answer is ignored.
#eval show IO Unit from do
  let r := Run.start |>.input (req expectPost)
  check (nextDeadline r.state == some (.continue, 10000)) s!"{repr (nextDeadline r.state)}"
  let r := r.at 10000 |>.input (.deadline .continue)
  check ((bytesOf r.last).startsWith "HTTP/1.1 417") "417 on timeout"
  let r := r.input (.continueDecided true)
  check r.last.isEmpty "late decision ignored"

-- Asked only once the earlier response is written.
#eval show IO Unit from do
  let r := Run.start |>.input (req (get "/a" ++ expectPost))
  let r := r.input (full "A")
  check (!has r.last "askContinue") "not yet"
  let r := r.input .written
  checkTags r #["askContinue"] "now"

/-! ## Backpressure -/

#eval show IO Unit from do
  let big := "".pushn 'x' 40000
  let r := Run.start |>.input (req (get "/big")) |>.input streamed
  let r := r.input (chunk big)
  check r.pulling "under the limit: pull"
  let r := r.input (chunk big)
  check (!r.pulling) "over the limit: wait"
  check (r.input (chunk big)).last.isEmpty "a chunk that was not pulled is ignored"
  let r := r.input .written
  check r.pulling "confirmed: pull again"

/-! ## Failures and shutdown -/

-- A shutdown while the handler runs: 503, and its late response is the interpreter's to release.
#eval show IO Unit from do
  let r := Run.start |>.input (req (get "/"))
  let r := r.input (.cancelled false)
  check ((bytesOf r.last).startsWith "HTTP/1.1 503") s!"503: {(bytesOf r.last).quote}"
  check (has r.last "abandonHandler") "abandoned"
  check (r.input (.cancelled false)).last.isEmpty "a second shutdown is ignored"
  let r := r.input (full "late")
  check r.last.isEmpty "the late response is ignored"
  let r := r.input .written
  checkCleanup r "shutdown"

-- A shutdown while a response streams stops it and releases its body.
#eval show IO Unit from do
  let r := Run.start |>.input (req (get "/")) |>.input streamed |>.input (chunk "a")
  let r := r.input (.cancelled false)
  check (has r.last "releaseResponse") s!"released: {tags r.last}"
  check (!r.pulling) "no more pulls"
  let r := r.input (chunk "late")
  check r.last.isEmpty "a pull answered after the release is ignored"
  let r := r.input .written
  checkCleanup r "shutdown while streaming"

-- The connection's own deadline: 408 when no response started.
#eval show IO Unit from do
  let r := Run.start |>.input (req (postPart "/slow" 10 "abc"))
  let r := r.input (.cancelled true)
  check ((bytesOf r.last).startsWith "HTTP/1.1 408") s!"408: {(bytesOf r.last).quote}"
  check (r.input (.cancelled true)).last.isEmpty "a second cancellation is ignored"

-- A failed write drops the connection.
#eval show IO Unit from do
  let r := Run.start |>.input (req (get "/")) |>.input streamed |>.input (chunk "a")
  let r := r.input (.writeFailed (.userError "broken pipe"))
  check (reports r.last == #["broken pipe"]) s!"{reports r.last}"
  check (has r.last "releaseResponse" && has r.last "close" && !lingered r.last) s!"{tags r.last}"
  checkCleanup r "write failure"

-- A failing handler: 500.
#eval show IO Unit from do
  let r := Run.start |>.input (req (get "/"))
  let r := r.input (.handlerFailed (.userError "boom"))
  check ((bytesOf r.last).startsWith "HTTP/1.1 500") s!"500: {(bytesOf r.last).quote}"
  check (reports r.log == #["boom"]) s!"{reports r.log}"
  let r := r.input .written
  checkCleanup r "handler failure"

-- A handler that returns an interim status as its final response: 500, reported.
#eval show IO Unit from do
  let r := Run.start |>.input (req (get "/"))
  let r := r.input (.responded { status := .«continue» } none #[] true)
  check ((bytesOf r.last).startsWith "HTTP/1.1 500") s!"500: {(bytesOf r.last).quote}"
  check ((reports r.log).size == 1) s!"{reports r.log}"

-- A failing response body: reported, released, closed after the flush.
#eval show IO Unit from do
  let r := Run.start |>.input (req (get "/")) |>.input streamed |>.input (chunk "a")
  let r := r.input (.failed (.userError "producer died"))
  check (reports r.last == #["producer died"]) s!"{reports r.last}"
  check (has r.last "releaseResponse" && !has r.last "close") s!"{tags r.last}"
  let r := r.input .written
  checkCleanup r "response failure"

-- The peer closes an idle connection.
#eval show IO Unit from do
  let r := Run.start |>.input (.received none)
  check (has r.last "close" && !has r.last "write") s!"closed: {tags r.last}"
  check (reports r.log).isEmpty "nothing to report"
  checkCleanup r "peer close"

-- A malformed request: an error response, reported once, and the connection lingers.
#eval show IO Unit from do
  let r := Run.start |>.input (req "BAD\r\n\r\n")
  check ((bytesOf r.last).startsWith "HTTP/1.1 4") s!"an error response: {(bytesOf r.last).quote}"
  check ((reports r.log).size == 1) s!"{reports r.log}"
  let r := r.input .written
  check (lingered r.log) "the peer may still be sending: linger"
  checkCleanup r "bad request"

/-! ## Inputs from sources that are not armed are ignored -/

#eval show IO Unit from do
  let r := Run.start |>.input (req (get "/"))
  for i in [Input.received none, .received (some "x".toUTF8), .pulled none,
      .pulled (some { data := "x".toUTF8 }), .bodyInterest true, .bodyInterest false,
      .continueDecided true, .written, .deadline .linger] do
    check (step r.cfg r.state r.now i).2.isEmpty s!"an input from a source that is not armed acted"

/-! ## Statements that hold by construction -/

example (cfg : Http.Config) (s : State) (now : Nat) (i : Input) (h : s.phase = .closed) :
    step cfg s now i = (s, #[]) :=
  step_closed cfg s now i h
