/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Http.Protocol.H1
public import Std.Http.Test.Assert
import Init.Data.String.Legacy

public section

/-!
# Drivers for the HTTP/1.1 machine tests

`MachineTester` is a chainable builder over `Machine dir`: each operation returns a new tester,
assertion failures accumulate, and `run` throws them as one error. The functions after it drive a
server machine through a request split into reads in a given way, and step a machine until it halts.
-/

open Std Http
open Std.Http.Protocol.H1

namespace Std.Http.Internal.Test

structure MachineTester (dir : Direction) where

  /--
  Human-readable name used in error messages.
  -/
  name : String

  /--
  The machine under test.
  -/
  machine : Machine dir

  /--
  Events and output produced by the most recent `step` or `pullBody`.
  -/
  lastStep : Option (StepResult dir) := none

  /--
  Body chunks collected by `drainBody` / `pullBody`.
  -/
  pulled : Array PulledChunk := #[]

  /--
  Cumulative wire output across all `step` calls.
  -/
  allOutput : ByteArray := .empty

  /--
  Accumulated assertion failures; `run` throws if non-empty.
  -/
  errors : Array String := #[]

namespace MachineTester

def addError (t : MachineTester dir) (msg : String) : MachineTester dir :=
  { t with errors := t.errors.push s!"[{t.name}] {msg}" }

def withLastStep
    (t : MachineTester dir) (ctx : String)
    (k : MachineTester dir → StepResult dir → MachineTester dir) : MachineTester dir :=
  match t.lastStep with
  | none => t.addError s!"{ctx}: no step result (call .step first)"
  | some step => k t step

/-- Create a new server-side tester (receives requests, sends responses). -/
def receiving (name : String) (config : Protocol.H1.Config := {}) : MachineTester .receiving :=
  { name, machine := { config } }

/-- Create a new client-side tester (sends requests, receives responses). -/
def sending (name : String) (config : Protocol.H1.Config := {}) : MachineTester .sending :=
  { name, machine := { config } }

/-- Feed a UTF-8 string to the machine. -/
def feed (t : MachineTester dir) (data : String) : MachineTester dir :=
  { t with machine := t.machine.feed data.toUTF8, lastStep := none }

/-- Feed raw bytes to the machine. -/
def feedBytes (t : MachineTester dir) (data : ByteArray) : MachineTester dir :=
  { t with machine := t.machine.feed data, lastStep := none }

/-- Run one step of the state machine and record the result. -/
def step (t : MachineTester dir) : MachineTester dir :=
  let (machine, stepResult) := t.machine.step
  let allOutput := t.allOutput ++ stepResult.output.toByteArray
  { t with machine, lastStep := some stepResult, allOutput }

/--
Pull at most one body chunk. Updates `pulled` and replaces `lastStep` with the
events emitted during the pull.
-/
def pullBody (t : MachineTester dir) : MachineTester dir :=
  let (machine, chunk?) := t.machine.pullBody
  let (machine, pullEvents) := machine.takeEvents
  let pulled := match chunk? with
    | some chunk => t.pulled.push chunk
    | none => t.pulled
  { t with machine, pulled, lastStep := some { events := pullEvents } }

/--
Drain all immediately-available body chunks.

The loop exits when `canPullBodyNow` becomes false (either the body is complete
or the machine stalls waiting for more data). The stall flag is set internally
by `pullBody`, so no explicit `remainingBytes` guard is needed.
-/
def drainBody (t : MachineTester dir) (fuel : Nat := 4096) : MachineTester dir := Id.run do
  let mut t := t
  let mut remaining := fuel
  while remaining > 0 && t.machine.canPullBodyNow do
    remaining := remaining - 1
    t := t.pullBody
  t

/-- Set the known outgoing body size (forwarded to the writer). -/
def setKnownSize (t : MachineTester dir) (size : Body.Length) : MachineTester dir :=
  { t with machine := t.machine.setKnownSize size }

/-- Signal EOF on the reader input (no more socket bytes will arrive). -/
def noMoreInput (t : MachineTester dir) : MachineTester dir :=
  { t with machine := t.machine.noMoreInput }

/-- Send a message head (request for `.sending`, response for `.receiving`). -/
def send (t : MachineTester dir) (head : Message.Head dir.swap) : MachineTester dir :=
  { t with machine := t.machine.send head }

/-- Signal that the application has finished writing the message body. -/
def userClosedBody (t : MachineTester dir) : MachineTester dir :=
  { t with machine := t.machine.userClosedBody }

/-- Resolve an `Expect: 100-continue` decision. No-op for `.sending` direction. -/
def canContinue (t : MachineTester dir) (status : Status) : MachineTester dir :=
  { t with machine := t.machine.canContinue status }

/-- Send an error response with `Connection: close` and shut down input. Only valid for `.receiving`. -/
def closeWithError (t : MachineTester .receiving) (status : Status) : MachineTester .receiving :=
  { t with machine := t.machine.closeWithError status }

/-- Enqueue body chunks into the writer buffer. -/
def sendData (t : MachineTester dir) (chunks : Array Chunk) : MachineTester dir :=
  { t with machine := t.machine.sendData chunks }

/-- Enqueue raw bytes as a single body chunk into the writer buffer. -/
def sendBytes (t : MachineTester dir) (data : ByteArray) : MachineTester dir :=
  t.sendData #[{ data, extensions := #[] }]

/-- Assert a predicate on the current machine. -/
def assert (t : MachineTester dir) (pred : Machine dir → Bool) (msg : String) : MachineTester dir :=
  if pred t.machine then t else t.addError msg

/-- Assert that `machine.error` is `none`. -/
def assertNoError (t : MachineTester dir) : MachineTester dir :=
  t.assert (fun m => m.error == none)
    s!"machine should have no error, got: {repr t.machine.error}"

/-- Assert that the machine has failed with the given error. -/
def assertFailedWith (t : MachineTester dir) (expected : Error) : MachineTester dir :=
  t.assert (fun m => m.error == some expected)
    s!"expected error {repr expected}, got {repr t.machine.error}"

/-- Assert that `canPullBodyNow` is true. -/
def assertCanPullBodyNow (t : MachineTester dir) : MachineTester dir :=
  t.assert (·.canPullBodyNow) "expected canPullBodyNow = true"

/-- Assert that the reader is in the `complete` state. -/
def assertReaderComplete (t : MachineTester dir) : MachineTester dir :=
  t.assert (·.isReaderComplete)
    s!"expected reader to be complete, state: {repr t.machine.reader.state}"

/-- Assert that the reader is in the `closed` state. -/
def assertReaderClosed (t : MachineTester dir) : MachineTester dir :=
  t.assert (·.isReaderClosed)
    s!"expected reader to be closed, state: {repr t.machine.reader.state}"

/-- Assert that `keepAlive` is true on the machine. -/
def assertKeepAlive (t : MachineTester dir) : MachineTester dir :=
  t.assert (·.keepAlive) "expected keepAlive = true"

/-- Assert that `keepAlive` is false on the machine. -/
def assertNotKeepAlive (t : MachineTester dir) : MachineTester dir :=
  t.assert (fun m => !m.keepAlive) "expected keepAlive = false"

/-- Assert that `isWaitingMessage` is true (writer in `waitingHeaders`, `!sentMessage`). -/
def assertIsWaitingMessage (t : MachineTester dir) : MachineTester dir :=
  t.assert (·.isWaitingMessage) "expected isWaitingMessage = true"

/-- Assert that `halted` is true (both reader and writer closed, no output). -/
def assertHalted (t : MachineTester dir) : MachineTester dir :=
  t.assert (·.halted) "expected machine to be halted"

/-- Assert that at least one event in the last step matches `pred`. -/
def assertHasEvent
    (t : MachineTester dir) (pred : Event dir → Bool) (msg : String) : MachineTester dir :=
  t.withLastStep "assertHasEvent" fun t step =>
    if step.events.any pred then t
    else t.addError s!"{msg}\n  events: {repr step.events}"

/-- Assert that no event in the last step matches `pred`. -/
def assertNoEvent
    (t : MachineTester dir) (pred : Event dir → Bool) (msg : String) : MachineTester dir :=
  t.withLastStep "assertNoEvent" fun t step =>
    if step.events.any pred then
      t.addError s!"{msg}\n  events: {repr step.events}"
    else t

/-- Assert that the last step contains an `endHeaders` event. -/
def assertHasEndHeaders (t : MachineTester dir) : MachineTester dir :=
  t.assertHasEvent (fun | .endHeaders _ => true | _ => false) "expected endHeaders event"

/-- Assert that the last step contains a `closeBody` event. -/
def assertHasCloseBody (t : MachineTester dir) : MachineTester dir :=
  t.assertHasEvent (fun | .closeBody => true | _ => false) "expected closeBody event"

/-- Assert that the last step contains a `next` event. -/
def assertHasNext (t : MachineTester dir) : MachineTester dir :=
  t.assertHasEvent (fun | .next => true | _ => false) "expected next event"

/-- Assert that the last step contains a `continue` event. -/
def assertHasContinue (t : MachineTester dir) : MachineTester dir :=
  t.assertHasEvent (fun | .«continue» => true | _ => false) "expected continue event"

/-- Inspect the `endHeaders` payload in the last step. -/
def onEndHeaders
    (t : MachineTester dir)
    (f : MachineTester dir → Message.Head dir → MachineTester dir) : MachineTester dir :=
  t.withLastStep "onEndHeaders" fun t step =>
    match step.events.findSome? (fun | .endHeaders h => some h | _ => none) with
    | none => t.addError "onEndHeaders: no endHeaders event in last step"
    | some head => f t head

/-- Assert that the cumulative output starts with the given ASCII string. -/
def assertOutputStartsWith (t : MachineTester dir) (pfx : String) (msg : String) : MachineTester dir :=
  let s := String.fromUTF8! t.allOutput
  if s.startsWith pfx then t
  else
    let preview := String.fromUTF8! (t.allOutput.extract 0 (min t.allOutput.size 120))
    t.addError s!"{msg}: expected output to start with {repr pfx}\n  got: {repr preview}"

/-- Assert that the cumulative output contains the given ASCII substring. -/
def assertOutputContains (t : MachineTester dir) (needle : String) (msg : String) : MachineTester dir :=
  if (String.fromUTF8! t.allOutput).contains needle then t
  else
    let preview := String.fromUTF8! (t.allOutput.extract 0 (min t.allOutput.size 160))
    t.addError s!"{msg}: expected output to contain {repr needle}\n  output: {repr preview}"

/-- Assert that the cumulative output does not contain the given ASCII substring. -/
def assertOutputNotContains (t : MachineTester dir) (needle : String) (msg : String) : MachineTester dir :=
  if (String.fromUTF8! t.allOutput).contains needle then
    let preview := String.fromUTF8! (t.allOutput.extract 0 (min t.allOutput.size 160))
    t.addError s!"{msg}: expected output NOT to contain {repr needle}\n  output: {repr preview}"
  else t

/-- Assert that the total bytes pulled so far equal `expected`. -/
def assertPulledBody (t : MachineTester dir) (expected : ByteArray) : MachineTester dir :=
  let got := t.pulled.foldl (fun acc c => acc ++ c.chunk.data) ByteArray.empty
  if got == expected then t
  else t.addError
    s!"body mismatch:\n  expected={String.fromUTF8! expected |>.quote}\n  got={String.fromUTF8! got |>.quote}"

/-- Assert that at least one chunk was pulled and the last one is `final`. -/
def assertLastChunkFinal (t : MachineTester dir) : MachineTester dir :=
  match t.pulled.back? with
  | none => t.addError "assertLastChunkFinal: no chunks pulled yet"
  | some chunk =>
    if chunk.final then t
    else t.addError "expected last pulled chunk to be final"

/-- Run a custom check on the current machine state. -/
def onMachine (t : MachineTester dir) (f : MachineTester dir → Machine dir → MachineTester dir) : MachineTester dir :=
  f t t.machine

/-- Throw if any assertion has failed; otherwise succeed. -/
def run (t : MachineTester dir) : IO Unit :=
  unless t.errors.isEmpty do
    throw <| IO.userError <| "\n".intercalate t.errors.toList

end MachineTester

/--
Steps `machine` `n` times and returns it with everything it wrote.
-/
def stepOutput {dir : Direction} (machine : Machine dir) (n : Nat := 4) : Machine dir × String := Id.run do
  let mut machine := machine
  let mut out := ByteArray.empty
  for _ in [0:n] do
    let (next, step) := machine.step
    machine := next
    out := out ++ step.output.toByteArray
  return (machine, String.fromUTF8! out)

/--
Steps `machine` until it halts. Returns everything it wrote and every event it emitted, or `none`
if it has not halted after `fuel` steps.
-/
def runToHalt {dir : Direction} (machine : Machine dir) (fuel : Nat := 16) :
    Option (String × Array (Event dir)) := Id.run do
  let mut machine := machine
  let mut out := ""
  let mut events := #[]
  for _ in [0:fuel] do
    let (next, step) := machine.step
    machine := next
    out := out ++ String.fromUTF8! step.output.toByteArray
    events := events ++ step.events
    if machine.halted then return some (out, events)
  return none

/--
What a server machine did with a request fed in pieces.
-/
structure Trace where
  machine : Machine .receiving
  events : Array (Event .receiving) := #[]
  output : ByteArray := .empty
  pulled : Array PulledChunk := #[]

/--
The body bytes pulled, in order.
-/
def Trace.body (t : Trace) : ByteArray :=
  t.pulled.foldl (fun acc c => acc ++ c.chunk.data) .empty

/--
Feeds `parts` to a server machine one read at a time, stepping after each and pulling at most one
body chunk, as a streaming caller does; then steps once more and drains the ready body.
-/
def feedParts (parts : Array ByteArray) (config : Protocol.H1.Config := {}) : Trace := Id.run do
  let mut machine : Machine .receiving := { config := config }
  let mut events : Array (Event .receiving) := #[]
  let mut output := ByteArray.empty
  let mut pulled : Array PulledChunk := #[]
  for part in parts do
    machine := machine.feed part
    let (machine', step) := machine.step
    machine := machine'
    events := events ++ step.events
    output := output ++ step.output.toByteArray
    -- An empty buffer is not handed to body parsing.
    if machine.canPullBodyNow && machine.reader.input.remainingBytes > 0 then
      let (machine', pulledNow?) := machine.pullBody
      let (machine', pullEvents) := machine'.takeEvents
      machine := machine'
      if let some pulledNow := pulledNow? then
        pulled := pulled.push pulledNow
      events := events ++ pullEvents
  let (machine', finalStep) := machine.step
  machine := machine'
  events := events ++ finalStep.events
  output := output ++ finalStep.output.toByteArray
  let mut fuel := 4096
  while fuel > 0 && machine.canPullBodyNow && machine.reader.input.remainingBytes > 0 do
    fuel := fuel - 1
    let (machine', pulledNow?) := machine.pullBody
    let (machine', pullEvents) := machine'.takeEvents
    machine := machine'
    events := events ++ pullEvents
    match pulledNow? with
    | some pulledNow => pulled := pulled.push pulledNow
    | none => break
  return { machine, events, output, pulled }

/--
`data` split into the reads `[0, i)` and `[i, size)`.
-/
def splitAt (data : ByteArray) (i : Nat) : Array ByteArray :=
  #[data.extract 0 i, data.extract i data.size]

/--
`data` split into one-byte reads.
-/
def eachByte (data : ByteArray) : Array ByteArray :=
  (Array.range data.size).map fun i => data.extract i (i + 1)

/--
`feedParts` with `data` split into two reads at `i`.
-/
def feedSplit (data : ByteArray) (i : Nat) (config : Protocol.H1.Config := {}) : Trace :=
  feedParts (splitAt data i) config

/--
`feedParts` with `data` fed one byte per read.
-/
def feedEachByte (data : ByteArray) (config : Protocol.H1.Config := {}) : Trace :=
  feedParts (eachByte data) config

/--
Feeds the first of `parts` and steps once, so the head is read; then feeds each later part and pulls
the body once after each, without stepping again. With `drainLast`, the last part is pulled until no
chunk comes out, since one read can hold several chunks.
-/
def feedPullOnly (parts : Array ByteArray) (config : Protocol.H1.Config := {}) (drainLast : Bool := false) :
    Trace := Id.run do
  let mut machine : Machine .receiving := { config := config }
  let mut events : Array (Event .receiving) := #[]
  let mut output := ByteArray.empty
  let mut pulled : Array PulledChunk := #[]
  for h : i in [0:parts.size] do
    machine := machine.feed parts[i]
    if i == 0 then
      let (machine', step) := machine.step
      machine := machine'
      events := events ++ step.events
      output := output ++ step.output.toByteArray
    let (machine', pulledNow?) := machine.pullBody
    let (machine', pullEvents) := machine'.takeEvents
    machine := machine'
    events := events ++ pullEvents
    if let some pulledNow := pulledNow? then
      pulled := pulled.push pulledNow
  if drainLast then
    let mut fuel := 4096
    while fuel > 0 && machine.canPullBodyNow do
      fuel := fuel - 1
      let (machine', pulledNow?) := machine.pullBody
      let (machine', pullEvents) := machine'.takeEvents
      machine := machine'
      events := events ++ pullEvents
      match pulledNow? with
      | some pulledNow => pulled := pulled.push pulledNow
      | none => break
  return { machine, events, output, pulled }

/--
Fails unless the trace read a whole message whose body is `want`: no failure, an `endHeaders`
event, a `needMoreData` event when `needMoreData` is set, the exact body, and, when there is a body,
a `closeBody` event and a final last chunk.
-/
def expectBody (t : Trace) (want : ByteArray) (needMoreData : Bool := true) : IO Unit := do
  ensure (!t.machine.failed) s!"machine ended failed with events:\n{repr t.events}"
  ensure (!t.events.any (· matches .failed _)) s!"unexpected failure events:\n{repr t.events}"
  ensure (t.events.any (· matches .endHeaders _)) s!"missing endHeaders event:\n{repr t.events}"
  if needMoreData then
    ensure (t.events.any (· matches .needMoreData _))
      s!"expected at least one needMoreData event:\n{repr t.events}"
  ensure (t.body == want)
    s!"body mismatch:\nexpected={(String.fromUTF8? want).getD "<binary>" |>.quote}\nactual={(String.fromUTF8? t.body).getD "<binary>" |>.quote}"
  if want.size > 0 || t.pulled.size > 0 then
    ensure (t.events.any (· matches .closeBody)) s!"missing closeBody event:\n{repr t.events}"
    ensure (t.pulled.any (·.final)) "expected at least one final pulled chunk"
    ensure ((t.pulled.back?.map (·.final)).getD false) "expected last pulled chunk to be final"

end Std.Http.Internal.Test
