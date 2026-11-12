/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Http.Server
public import Std.Async
import Init.Data.String.Legacy

public section

/-!
# Assertions for the Std.Http tests

Table-driven checks shared by the `tests/async/elab/async_http_*` files. `checkCases` runs every
case of a table under `hangGuard` and reports each failing case by its label. Deadlines are
multiplied by `LEAN_TEST_TIME_SCALE`, which the sanitizer presets set, so a guard only detects
hangs and never asserts a duration.
-/

open Std.Async
open Std Http

namespace Std.Http.Internal.Test

/--
The factor applied to every test deadline: `LEAN_TEST_TIME_SCALE` when it is a positive number,
otherwise 1.
-/
def timeScale : IO Nat := do
  match (← IO.getEnv "LEAN_TEST_TIME_SCALE").bind String.toNat? with
  | some n => pure (if n == 0 then 1 else n)
  | none => pure 1

private partial def awaitUntil {α : Type} (task : Task (Except IO.Error α)) (deadline : Nat)
    (pause : UInt32) : IO (Option α) := do
  if (← IO.getTaskState task) == .finished then
    match ← IO.wait task with
    | .ok x => pure (some x)
    | .error e => throw e
  else if (← IO.monoMsNow) ≥ deadline then
    pure none
  else
    IO.sleep pause
    awaitUntil task deadline (min (pause * 2) 10)

/--
Runs `act`, failing with `name` if it has not finished after `ms × timeScale` milliseconds.
-/
def hangGuard {α : Type} (name : String) (ms : Nat) (act : IO α) : IO α := do
  let scale ← timeScale
  let task ← IO.asTask act
  match ← awaitUntil task ((← IO.monoMsNow) + ms * scale) 1 with
  | some x => pure x
  | none =>
    IO.cancel task
    throw <| IO.userError s!"'{name}' did not finish within {ms * scale} ms"

/--
Fails with `msg` unless `cond` holds.
-/
def ensure (cond : Bool) (msg : String) : IO Unit :=
  unless cond do throw <| IO.userError msg

/--
`repr a` on a single line, for comparing whole values against a string in a table.
-/
def reprLine {α : Type} [Repr α] (a : α) : String :=
  (repr a).pretty 100000

/--
Fails unless `got == want`, showing both values.
-/
def expectEq {α : Type} [BEq α] [Repr α] (what : String) (got want : α) : IO Unit :=
  unless got == want do
    throw <| IO.userError s!"{what}: expected {reprLine want}, got {reprLine got}"

/--
How a table case names itself in failure messages.
-/
class CaseLabel (α : Type) where
  label : α → String

instance : CaseLabel String := ⟨id⟩

instance {β : Type} : CaseLabel (String × β) := ⟨(·.1)⟩

/--
Runs `run` on every case under `hangGuard` (`ms` per case) and fails once at the end, listing every
failing case by its label. A case that hangs fails like any other.
-/
def checkCases {α : Type} [CaseLabel α] (group : String) (cases : Array α) (run : α → IO Unit)
    (ms : Nat := 10000) : IO Unit := do
  let mut failures : Array String := #[]
  for c in cases do
    let label := CaseLabel.label c
    try hangGuard s!"{group}: {label}" ms (run c)
    catch e => failures := failures.push s!"  {label}: {e}"
  unless failures.isEmpty do
    throw <| IO.userError
      s!"[{group}] {failures.size} of {cases.size} cases failed:\n{"\n".intercalate failures.toList}"

/--
A deterministic SplitMix64 generator.
-/
structure Rng where
  state : UInt64

namespace Rng

/--
Returns the next 64-bit output and the advanced generator.
-/
def next (g : Rng) : UInt64 × Rng :=
  let s := g.state + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), ⟨s⟩)

/--
Returns a number in `[0, n)`, or 0 when `n = 0`.
-/
def below (g : Rng) (n : Nat) : Nat × Rng :=
  let (x, g) := g.next
  (if n == 0 then 0 else x.toNat % n, g)

end Rng

/--
A raw HTTP/1.x request. `host := none` omits the `Host` field; `extra` holds complete field lines
(each ending in CRLF) and goes after `Host`.
-/
def rawRequest (method : String := "GET") (target : String := "/") (version : String := "HTTP/1.1")
    (host : Option String := some "example.com") (extra : String := "") (body : String := "") :
    String :=
  let hostLine := match host with
    | some h => s!"Host: {h}\x0d\n"
    | none => ""
  s!"{method} {target} {version}\x0d\n{hostLine}{extra}\x0d\n{body}"

/--
The exact response a server writes for `Response.ok |>.text content` on a connection that closes
after it.
-/
def okResponse (content : String := "ok") (close : Bool := true) : String :=
  let connection := if close then "Connection: close\x0d\n" else ""
  s!"HTTP/1.1 200 OK\x0d\nContent-Type: text/plain; charset=utf-8\x0d\nServer: LeanHTTP/1.1\x0d\n" ++
    s!"{connection}Content-Length: {content.utf8ByteSize}\x0d\n\x0d\n{content}"

/--
The server config of the table helpers: a short lingering timeout and no `Date` field.
-/
def testConfig : Config :=
  { lingeringTimeout := 1000, generateDate := false }

/--
Sends `raw` to `serveConnection` over a mock transport and returns every byte the server wrote.
With `closeInput`, the client's side is closed after `raw`, so the server sees EOF.
-/
def serveBytes {σ : Type} [Server.Handler σ] (raw : ByteArray) (handler : σ)
    (config : Config := testConfig) (closeInput : Bool := false) : IO ByteArray := do
  let (client, server) ← Mock.new
  Async.block do
    client.send raw
    if closeInput then client.getSendChan.close
    Server.serveConnection server handler config |>.run
    return (← client.recv?).getD .empty

/--
`serveBytes` with the UTF-8 bytes of `raw`.
-/
def serveRaw {σ : Type} [Server.Handler σ] (raw : String) (handler : σ)
    (config : Config := testConfig) (closeInput : Bool := false) : IO ByteArray :=
  serveBytes raw.toUTF8 handler config closeInput

/--
`serveRaw` with the client's side closed after `raw`.
-/
def serveRawClosed {σ : Type} [Server.Handler σ] (raw : String) (handler : σ)
    (config : Config := testConfig) : IO ByteArray :=
  serveRaw raw handler config (closeInput := true)

/--
A request as a recording handler saw it.
-/
structure Seen where
  method : String
  target : String
  body : String
  deriving Repr, BEq

private structure Recorder where
  seen : IO.Ref (Array Seen)
  readBody : Bool

private instance : Server.Handler Recorder where
  onRequest self req := do
    let body ← if self.readBody then req.body.readAll else pure ""
    self.seen.modify (·.push ⟨toString req.line.method, toString req.line.uri, body⟩)
    Response.ok |>.text "ok"

/--
Serves `raw` with a handler that records every request it is called with and answers `200 ok`.
Returns the bytes written and the recorded requests, in order.
-/
def serveRecording (raw : String) (readBody : Bool := true) (config : Config := testConfig)
    (closeInput : Bool := false) : IO (ByteArray × Array Seen) := do
  let seen ← IO.mkRef #[]
  let response ← serveRaw raw ({ seen, readBody } : Recorder) config closeInput
  return (response, ← seen.get)

/--
What a response must look like.
-/
inductive Want where
  /-- These exact bytes. -/
  | exact (response : String)
  /-- A response that starts with this prefix, e.g. `"HTTP/1.1 200"`. -/
  | status (prefix_ : String)
  /-- A single `200` response whose content is exactly this. -/
  | body (content : String)
  /-- The bytes contain this. -/
  | contains (needle : String)
  /-- The bytes do not contain this. -/
  | absent (needle : String)
  /-- Exactly this many `HTTP/1.1 ` status lines. -/
  | responses (n : Nat)
  /-- Every one of these. -/
  | all (wants : List Want)

namespace Want

private def text (response : ByteArray) : String :=
  String.fromUTF8? response |>.getD s!"<{response.size} bytes, not UTF-8>"

/--
Fails unless `response` matches `want`.
-/
partial def check (want : Want) (response : ByteArray) : IO Unit := do
  let t := text response
  match want with
  | .exact r =>
    ensure (t == r) s!"expected:\n{r.quote}\ngot:\n{t.quote}"
  | .status p =>
    ensure (t.startsWith p) s!"expected status {p.quote}, got:\n{t.quote}"
  | .body c =>
    ensure (t.startsWith "HTTP/1.1 200" && (t.splitOn "HTTP/1.1 ").length == 2 &&
        (t.splitOn "\x0d\n\x0d\n").drop 1 == [c])
      s!"expected one 200 response with content {c.quote}, got:\n{t.quote}"
  | .contains n =>
    ensure (t.contains n) s!"expected to contain {n.quote}, got:\n{t.quote}"
  | .absent n =>
    ensure (!t.contains n) s!"expected NOT to contain {n.quote}, got:\n{t.quote}"
  | .responses n =>
    let got := (t.splitOn "HTTP/1.1 ").length - 1
    ensure (got == n) s!"expected {n} HTTP/1.1 responses, got {got}:\n{t.quote}"
  | .all ws => ws.forM (check · response)

end Want

/--
Serves `raw` with `handler` and checks the response against `want`.
-/
def checkHandler {σ : Type} [Server.Handler σ] (raw : String) (handler : σ) (want : Want)
    (config : Config := testConfig) (closeInput : Bool := false) : IO Unit := do
  want.check (← serveRaw raw handler config closeInput)

end Std.Http.Internal.Test
