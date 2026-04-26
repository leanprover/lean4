/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Leonardo de Moura
-/
module

prelude
public import Lean.Elab.Exception
public import Lean.Log

public section

/-!
# Trace messages

Trace messages explain to the user what problem Lean solved and what steps it took.
Think of trace messages like a figure in a paper.

They are shown in the editor as a collapsible tree,
usually as `[class.name] message ▸`.
Every trace node has a class name, a message, and an array of children.
This module provides the API to produce trace messages,
the key entry points are:
- ``registerTraceClass `class.name`` registers a trace class
- ``withTraceNode `class.name (fun result => return msg) do body`
  produces a trace message containing the trace messages in `body` as children
- `trace[class.name] msg` produces a trace message without children

Users can enable trace options for a class using
`set_option trace.class.name true`.
This only enables trace messages for the `class.name` trace class
as well as child classes that are explicitly marked as inherited
(see `registerTraceClass`).

Internally, trace messages are stored as `MessageData`:
`.trace cls msg #[.trace .., .trace ..]`

When writing trace messages,
try to follow these guidelines:
1. **Expansion progressively increases detail.**
  Each level of expansion (of the trace node in the editor) should reveal more details.
  For example, the unexpanded node should show the top-level goal.
  Expanding it should show a list of steps.
  Expanding one of the steps then shows what happens during that step.
2. **One trace message per step.**
  The `[trace.class]` marker functions as a visual bullet point,
  making it easy to identify the different steps at a glance.
3. **Outcome first.**
  The top-level trace message should already show whether the action failed or succeeded,
  as opposed to a "success" trace message that comes pages later.
4. **Be concise.**
  Keep messages short.
  Avoid repetitive text.
  (This is also why the editor plugins abbreviate the common prefixes.)
5. **Emoji are concisest.**
  Several helper functions in this module help with a consistent emoji language.
6. **Good defaults.**
  Setting `set_option trace.Meta.synthInstance true` (etc.)
  should produce great trace messages out-of-the-box,
  without needing extra options to tweak it.
-/

namespace Lean

structure TraceElem where
  ref : Syntax
  msg : MessageData
  deriving Inhabited

structure TraceState where
  /-- Thread ID, used by `trace.profiler.output`. -/
  tid     : UInt64 := 0
  traces  : PersistentArray TraceElem := {}
  deriving Inhabited

builtin_initialize inheritedTraceOptions : IO.Ref (Std.HashSet Name) ← IO.mkRef ∅

class MonadTrace (m : Type → Type) where
  modifyTraceState : (TraceState → TraceState) → m Unit
  getTraceState    : m TraceState
  /--
  Should return the value of `inheritedTraceOptions.get`, which does not change after
  initialization. As `IO.Ref.get` may be too expensive on frequent and multi-threaded access, the
  value may want to be cached, which is done in the stdlib in `CoreM`.
  -/
  getInheritedTraceOptions : m (Std.HashSet Name) := by exact inheritedTraceOptions.get

export MonadTrace (getTraceState modifyTraceState)

instance (m n) [MonadLift m n] [MonadTrace m] : MonadTrace n where
  modifyTraceState := fun f => liftM (modifyTraceState f : m _)
  getTraceState    := liftM (getTraceState : m _)
  getInheritedTraceOptions := liftM (MonadTrace.getInheritedTraceOptions : m _)

variable {α : Type} {m : Type → Type} [Monad m] [MonadTrace m] [MonadOptions m] [MonadLiftT IO m]

def printTraces : m Unit := do
  for {msg, ..} in (← getTraceState).traces do
    IO.println (← msg.format.toIO)

def resetTraceState : m Unit :=
  modifyTraceState (fun _ => {})

@[inline] def checkTraceOption (inherited : Std.HashSet Name) (opts : Options) (cls : Name) : Bool :=
  opts.hasTrace && go (`trace ++ cls)
where
  go (opt : Name) : Bool :=
    if let some enabled := opts.get? opt then
      enabled
    else if let .str parent _ := opt then
      inherited.contains opt && go parent
    else
      false

/-- Determine if tracing is available for a given class, checking ancestor classes if appropriate. -/
@[inline]
def isTracingEnabledFor (cls : Name) : m Bool := do
  return checkTraceOption (← MonadTrace.getInheritedTraceOptions) (← getOptions) cls

@[export lean_is_trace_class_enabled]
private def isTracingEnabledForExport (opts : Options) (cls : Name) : BaseIO Bool := do
  -- Replicate `checkTraceOption` fast path to make sure it happens before `IORef.get` (which
  -- itself is slower than `MonadTrace.getInheritedTraceOptions` but at least that's only on the
  -- slow path).
  if !opts.hasTrace then
    return false
  return checkTraceOption (← inheritedTraceOptions.get) opts cls

@[inline] def getTraces : m (PersistentArray TraceElem) := do
  let s ← getTraceState
  pure s.traces

@[inline] def modifyTraces (f : PersistentArray TraceElem → PersistentArray TraceElem) : m Unit :=
  modifyTraceState fun s => { s with traces := f s.traces }

@[inline] def setTraceState (s : TraceState) : m Unit :=
  modifyTraceState fun _ => s

private def getResetTraces : m (PersistentArray TraceElem) := do
  let oldTraces ← getTraces
  modifyTraces fun _ => {}
  pure oldTraces

section
variable [MonadRef m] [AddMessageContext m] [MonadOptions m]

def addRawTrace (msg : MessageData) : m Unit := do
  let ref ← getRef
  let msg ← addMessageContext msg
  modifyTraces (·.push { ref, msg })

def addTrace (cls : Name) (msg : MessageData) : m Unit := do
  let ref ← getRef
  let msg ← addMessageContext msg
  modifyTraces (·.push { ref, msg := .trace { collapsed := false, cls } msg #[] })

@[inline] def trace (cls : Name) (msg : Unit → MessageData) : m Unit := do
  if (← isTracingEnabledFor cls) then
    addTrace cls (msg ())

@[inline] def traceM (cls : Name) (mkMsg : m MessageData) : m Unit := do
  if (← isTracingEnabledFor cls) then
    let msg ← mkMsg
    addTrace cls msg

private def addTraceNode (oldTraces : PersistentArray TraceElem)
    (data : TraceData) (ref : Syntax) (msg : MessageData) : m Unit :=
  withRef ref do
  let msg := .trace data msg ((← getTraces).toArray.map (·.msg))
  let msg ← addMessageContext msg
  modifyTraces fun _ =>
    oldTraces.push { ref, msg }

register_builtin_option trace.profiler : Bool := {
  defValue := false
  descr    :=
    "activate nested traces with execution time above `trace.profiler.threshold` and annotate with \
    time"
}

register_builtin_option trace.profiler.threshold : Nat := {
  defValue := 10
  descr    :=
    "threshold in milliseconds (or heartbeats if `trace.profiler.useHeartbeats` is true), \
    traces below threshold will not be activated"
}

register_builtin_option trace.profiler.useHeartbeats : Bool := {
  defValue := false
  descr    :=
    "if true, measure and report heartbeats instead of seconds"
}

register_builtin_option trace.profiler.output : String := {
  defValue := ""
  descr    :=
    "output `trace.profiler` data in Firefox Profiler-compatible format to given file path"
}

register_builtin_option trace.profiler.serve : Bool := {
  defValue := false
  descr    :=
    "serve the `trace.profiler` data over HTTP and open it in `https://profiler.firefox.com`; \
     blocks until interrupted with Ctrl+C"
}

/--
True if the `trace.profiler` data should be retained for export - either to a file
(`trace.profiler.output`) or via the local HTTP server (`trace.profiler.serve`). When true, code
that would otherwise consume the trace state as messages must leave it intact.
-/
@[inline] def trace.profiler.isExporting (opts : Options) : Bool :=
  (trace.profiler.output.get? opts).isSome || trace.profiler.serve.get opts

register_builtin_option trace.profiler.output.pp : Bool := {
  defValue := false
  descr    :=
    "if false, limit text in exported trace nodes to trace class name and `TraceData.tag`, if any

This is useful when we are interested in the time taken by specific subsystems instead of specific \
invocations, which is the common case."
}

@[inline] private def withStartStop [Monad m] [MonadLiftT BaseIO m] (opts : Options) (act : m α) :
    m (α × Float × Float) := do
  if trace.profiler.useHeartbeats.get opts then
    let start ← IO.getNumHeartbeats
    let a ← act
    let stop ← IO.getNumHeartbeats
    return (a, start.toFloat, stop.toFloat)
  else
    let start ← IO.monoNanosNow
    let a ← act
    let stop ← IO.monoNanosNow
    return (a, start.toFloat / 1000000000, stop.toFloat / 1000000000)

@[inline] def trace.profiler.threshold.unitAdjusted (o : Options) : Float :=
  if trace.profiler.useHeartbeats.get o then
    (trace.profiler.threshold.get o).toFloat
  else
    -- milliseconds to seconds
    (trace.profiler.threshold.get o).toFloat / 1000

/--
`MonadExcept` variant that is expected to catch all exceptions of the given type in case the
standard instance doesn't.

In most circumstances, we want to let runtime exceptions during term elaboration bubble up to the
command elaborator (see `Core.tryCatch`). However, in a few cases like building the trace tree, we
really need to handle (and then re-throw) every exception lest we end up with a broken tree.
-/
class MonadAlwaysExcept (ε : outParam (Type u)) (m : Type u → Type v) where
  except : MonadExceptOf ε m

-- instances sufficient for inferring `MonadAlwaysExcept` for the elaboration monads

instance : MonadAlwaysExcept ε (EIO ε) where
  except := inferInstance

instance [always : MonadAlwaysExcept ε m] : MonadAlwaysExcept ε (StateT σ m) where
  except := let _ := always.except; inferInstance

instance [always : MonadAlwaysExcept ε m] : MonadAlwaysExcept ε (StateRefT' ω σ m) where
  except := let _ := always.except; inferInstance

instance [always : MonadAlwaysExcept ε m] : MonadAlwaysExcept ε (ReaderT ρ m) where
  except := let _ := always.except; inferInstance

instance [always : MonadAlwaysExcept ε m] [STWorld ω m] [BEq α] [Hashable α] :
    MonadAlwaysExcept ε (MonadCacheT α β m) where
  except := let _ := always.except; inferInstance

def bombEmoji := "💥️"
def checkEmoji := "✅️"
def crossEmoji := "❌️"

/-- Convert a `TraceResult` to its emoji representation. -/
def TraceResult.toEmoji : TraceResult → String
  | .success => checkEmoji
  | .failure => crossEmoji
  | .error   => bombEmoji

/-- Convert an `Except` result to a `TraceResult`.
`Except.error` always maps to `.error`.
For `Bool`, `.ok false` maps to `.failure`. For `Option`, `.ok none` maps to `.failure`. -/
class ExceptToTraceResult (ε α : Type) where
  toTraceResult : Except ε α → TraceResult

instance : ExceptToTraceResult ε Bool where
  toTraceResult
    | .error _ => .error
    | .ok true => .success
    | .ok false => .failure

instance : ExceptToTraceResult ε (Option α) where
  toTraceResult
    | .error _ => .error
    | .ok (some _) => .success
    | .ok none => .failure

instance (priority := low) : ExceptToTraceResult ε α where
  toTraceResult
    | .error _ => .error
    | .ok _ => .success

/-- Convert an `Except` to a `TraceResult` using the `ExceptToTraceResult` instance. -/
def _root_.Except.toTraceResult [ExceptToTraceResult ε α] (e : Except ε α) : TraceResult :=
  ExceptToTraceResult.toTraceResult e

/-- Run the provided action `k`, and log its execution within a trace node.

The message is produced after the action completes, and has access to its return value.
If it is more convenient to produce the message as part of the computation,
then `Lean.withTraceNode'` can be used instead.
If profiling is enabled, this will also log the runtime of `k`.

The class `ExceptToTraceResult` is used to convert the result produced by `k` into a `TraceResult`
(success/failure/error), which is stored in `TraceData.result?` and also used to select the
emoji prefix (✅️/❌️/💥️). A typical invocation might be:
```lean4
withTraceNode `isPosTrace
    (msg := fun _ => return m!"checking positivity") do
  return 0 < x
```

The `cls`, `collapsed`, and `tag` arguments are forwarded to the constructor of `TraceData`.
-/
@[inline]
def withTraceNode [always : MonadAlwaysExcept ε m] [MonadLiftT BaseIO m]
    [ExceptToTraceResult ε α] (cls : Name)
    (msg : Except ε α → m MessageData) (k : m α) (collapsed := true) (tag := "") : m α := do
  let opts ← getOptions
  if !opts.hasTrace then
    return (← k)
  let clsEnabled ← isTracingEnabledFor cls
  unless clsEnabled || trace.profiler.get opts do
    return (← k)
  let oldTraces ← getResetTraces
  let resStartStop ← withStartStop opts <| let _ := always.except; observing k
  postCallback opts clsEnabled oldTraces msg resStartStop
where
  postCallback (opts : Options) (clsEnabled oldTraces msg resStartStop) : m α := do
    let _ := always.except
    let (res, start, stop) := resStartStop
    let aboveThresh := trace.profiler.get opts &&
      stop - start > trace.profiler.threshold.unitAdjusted opts
    unless clsEnabled || aboveThresh do
      modifyTraces (oldTraces ++ ·)
      return (← MonadExcept.ofExcept res)
    let ref ← getRef
    let mut m ← try msg res catch _ => pure m!"<exception thrown while producing trace node message>"
    let result := res.toTraceResult
    m := m!"{result.toEmoji} {m}"
    let mut data : TraceData := { cls, collapsed, tag, result? := some result }
    if trace.profiler.get opts then
      data := { data with startTime := start, stopTime := stop }
    addTraceNode oldTraces data ref m
    MonadExcept.ofExcept res

/-- A version of `Lean.withTraceNode` which allows generating the message within the computation. -/
@[inline]
def withTraceNode' [MonadAlwaysExcept Exception m] [MonadLiftT BaseIO m] (cls : Name)
    (k : m (α × MessageData)) (collapsed := true) (tag := "") : m α :=
  let msg := fun
    | .ok (_, msg) => return msg
    | .error err => return err.toMessageData
  Prod.fst <$> withTraceNode cls msg k collapsed tag

end

/--
Registers a trace class.

By default, trace classes are not inherited;
that is, `set_option trace.foo true` does not imply `set_option trace.foo.bar true`.
Calling ``registerTraceClass `foo.bar (inherited := true)`` enables this inheritance
on an opt-in basis.
-/
def registerTraceClass (traceClassName : Name) (inherited := false) (ref : Name := by exact decl_name%) : IO Unit := do
  let optionName := `trace ++ traceClassName
  registerOption optionName {
    name := optionName
    declName := ref
    defValue := false
    descr := "enable/disable tracing for the given module and submodules"
  }
  if inherited then
    inheritedTraceOptions.modify (·.insert optionName)

private meta def expandTraceMacro (id : Syntax) (s : Syntax) : MacroM (TSyntax `doElem) := do
  let msg ← if s.getKind == interpolatedStrKind then `(m! $(⟨s⟩)) else `(($(⟨s⟩) : MessageData))
  `(doElem| do
    let cls := $(quote id.getId.eraseMacroScopes)
    if (← Lean.isTracingEnabledFor cls) then
      Lean.addTrace cls $msg)

macro "trace[" id:ident "]" s:(interpolatedStr(term) <|> term) : doElem => do
  expandTraceMacro id s.raw


/--
Similar to `withTraceNode`, but msg is constructed **before** executing `k`.
This is important when debugging methods such as `isDefEq`, and we want to generate the message
before `k` updates the metavariable assignment. The class `ExceptToTraceResult` is used to convert
the result produced by `k` into a `TraceResult` (success/failure/error), which is stored in
`TraceData.result?` and also used to select the emoji prefix (✅️/❌️/💥️).

TODO: find better name for this function.
-/
@[inline]
def withTraceNodeBefore [MonadRef m] [AddMessageContext m] [MonadOptions m]
    [always : MonadAlwaysExcept ε m] [MonadLiftT BaseIO m] [ExceptToTraceResult ε α] (cls : Name)
    (msg : Unit → m MessageData) (k : m α) (collapsed := true) (tag := "") : m α := do
  let opts ← getOptions
  if !opts.hasTrace then
    return (← k)
  let clsEnabled ← isTracingEnabledFor cls
  unless clsEnabled || trace.profiler.get opts do
    return (← k)
  let oldTraces ← getResetTraces
  let ref ← getRef
  -- make sure to preserve context *before* running `k`
  let msg ← withRef ref do addMessageContext (← msg ())
  let resStartStop ← withStartStop opts <| let _ := always.except; observing k
  postCallback opts clsEnabled oldTraces ref msg resStartStop
where
  postCallback (opts : Options) (clsEnabled oldTraces ref msg resStartStop) : m α := do
    let _ := always.except
    let (res, start, stop) := resStartStop
    let aboveThresh := trace.profiler.get opts &&
      stop - start > trace.profiler.threshold.unitAdjusted opts
    unless clsEnabled || aboveThresh do
      modifyTraces (oldTraces ++ ·)
      return (← MonadExcept.ofExcept res)
    let result := res.toTraceResult
    let mut msg := m!"{result.toEmoji} {msg}"
    let mut data : TraceData := { cls, collapsed, tag, result? := some result }
    if trace.profiler.get opts then
      data := { data with startTime := start, stopTime := stop }
    addTraceNode oldTraces data ref msg
    MonadExcept.ofExcept res

def addTraceAsMessages [Monad m] [MonadRef m] [MonadLog m] [MonadTrace m] : m Unit := do
  if trace.profiler.isExporting (← getOptions) then
    -- do not add trace messages if the profile is being exported (`trace.profiler.output` or
    -- `trace.profiler.serve`) as it would be redundant, pretty printing the trace messages is
    -- expensive, and `getResetTraces` would consume the data we want to export
    return
  let traces ← getResetTraces
  if traces.isEmpty then
    return
  let mut pos2traces : Std.HashMap (String.Pos.Raw × String.Pos.Raw) (Array MessageData) := ∅
  for traceElem in traces do
    let ref := replaceRef traceElem.ref (← getRef)
    let pos := ref.getPos?.getD 0
    let endPos := ref.getTailPos?.getD pos
    pos2traces := pos2traces.insert (pos, endPos) <| pos2traces.getD (pos, endPos) #[] |>.push traceElem.msg
  let traces' := pos2traces.toArray.qsort fun ((a, _), _) ((b, _), _) => a < b
  for ((pos, endPos), traceMsg) in traces' do
    -- cmdline and info view differ in how they insert newlines in between trace nodes so we just
    -- put them in a synthetic root node for now and let the rendering functions handle this case
    let data := .tagged `trace <| .trace { cls := .anonymous } .nil traceMsg
    logMessage <| Elab.mkMessageCore (← getFileName) (← getFileMap) data .information pos endPos

builtin_initialize
  registerTraceClass `debug

end Lean
