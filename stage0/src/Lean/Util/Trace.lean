/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Leonardo de Moura
-/
import Lean.Exception

/-!
# Trace messages

Trace messages explain to the user what problem Lean solved and what steps it took.
Think of trace messages like a figure in a paper.

They are shown in the editor as a collapsible tree,
usually as `[class.name] message ▸`.
Every trace node has a class name, a message, and an array of children.
This module provides the API to produce trace messages,
the key entry points are:
- ``registerTraceMessage `class.name`` registers a trace class
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
  traces  : PersistentArray TraceElem := {}
  deriving Inhabited

builtin_initialize inheritedTraceOptions : IO.Ref (HashSet Name) ← IO.mkRef ∅

class MonadTrace (m : Type → Type) where
  modifyTraceState : (TraceState → TraceState) → m Unit
  getTraceState    : m TraceState

export MonadTrace (getTraceState modifyTraceState)

instance (m n) [MonadLift m n] [MonadTrace m] : MonadTrace n where
  modifyTraceState := fun f => liftM (modifyTraceState f : m _)
  getTraceState    := liftM (getTraceState : m _)

variable {α : Type} {m : Type → Type} [Monad m] [MonadTrace m] [MonadOptions m] [MonadLiftT IO m]

def printTraces : m Unit := do
  for {msg, ..} in (← getTraceState).traces do
    IO.println (← msg.format)

def resetTraceState : m Unit :=
  modifyTraceState (fun _ => {})

private def checkTraceOption (inherited : HashSet Name) (opts : Options) (cls : Name) : Bool :=
  !opts.isEmpty && go (`trace ++ cls)
where
  go (opt : Name) : Bool :=
    if let some enabled := opts.get? opt then
      enabled
    else if let .str parent _ := opt then
      inherited.contains opt && go parent
    else
      false

def isTracingEnabledFor (cls : Name) : m Bool := do
  let inherited ← (inheritedTraceOptions.get : IO _)
  pure (checkTraceOption inherited (← getOptions) cls)

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
  modifyTraces (·.push { ref, msg := .trace cls msg #[] })

@[inline] def trace (cls : Name) (msg : Unit → MessageData) : m Unit := do
  if (← isTracingEnabledFor cls) then
    addTrace cls (msg ())

@[inline] def traceM (cls : Name) (mkMsg : m MessageData) : m Unit := do
  if (← isTracingEnabledFor cls) then
    let msg ← mkMsg
    addTrace cls msg

private def addTraceNode (oldTraces : PersistentArray TraceElem)
    (cls : Name) (ref : Syntax) (msg : MessageData) (collapsed : Bool) : m Unit :=
  withRef ref do
  let msg ← addMessageContext msg
  modifyTraces fun newTraces =>
    oldTraces.push { ref, msg := .trace cls msg (newTraces.toArray.map (·.msg)) collapsed }

def withTraceNode [MonadExcept ε m] (cls : Name) (msg : Except ε α → m MessageData) (k : m α)
    (collapsed := true) : m α := do
  if !(← isTracingEnabledFor cls) then
    k
  else
    let ref ← getRef
    let oldTraces ← getResetTraces
    let res ← observing k
    addTraceNode oldTraces cls ref (← msg res) collapsed
    MonadExcept.ofExcept res

def withTraceNode' [MonadExcept Exception m] (cls : Name) (k : m (α × MessageData)) (collapsed := true) : m α :=
  let msg := fun
    | .ok (_, msg) => return msg
    | .error err => return err.toMessageData
  Prod.fst <$> withTraceNode cls msg k collapsed

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
    declName := ref
    group := "trace"
    defValue := false
    descr := "enable/disable tracing for the given module and submodules"
  }
  if inherited then
    inheritedTraceOptions.modify (·.insert optionName)

macro "trace[" id:ident "]" s:(interpolatedStr(term) <|> term) : doElem => do
  let msg ← if s.raw.getKind == interpolatedStrKind then `(m! $(⟨s⟩)) else `(($(⟨s⟩) : MessageData))
  `(doElem| do
    let cls := $(quote id.getId.eraseMacroScopes)
    if (← Lean.isTracingEnabledFor cls) then
      Lean.addTrace cls $msg)

def bombEmoji := "💥"
def checkEmoji := "✅"
def crossEmoji := "❌"

def exceptBoolEmoji : Except ε Bool → String
  | .error _ => bombEmoji
  | .ok true => checkEmoji
  | .ok false => crossEmoji

def exceptOptionEmoji : Except ε (Option α) → String
  | .error _ => bombEmoji
  | .ok (some _) => checkEmoji
  | .ok none => crossEmoji

end Lean
