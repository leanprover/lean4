module

meta import Lean.PostprocessTraces

/-!
Tests for stored traces: the `store_traces_as t in cmd` command, the `#trace_roots t` and
`#postprocess_traces t post` commands that inspect a stored trace without re-running `cmd`, and
the `Lean.PostprocessTraces.StoredTrace` API for metaprograms.
-/

open scoped Lean.PostprocessTraces

-- `store_traces_as` reports the trace unchanged and stores it for later inspection.
/--
trace: [Meta.synthInstance] ✅️ Inhabited (Nat × Bool)
  [Meta.synthInstance] ✅️ new goal Inhabited (Nat × Bool)
    [Meta.synthInstance.instances] #[@instInhabitedOfMonad, @instInhabitedProd]
  [Meta.synthInstance.apply] ✅️ apply @instInhabitedProd to Inhabited (Nat × Bool)
    [Meta.synthInstance.tryResolve] ✅️ Inhabited (Nat × Bool) ≟ Inhabited (Nat × Bool)
    [Meta.synthInstance] ✅️ new goal Inhabited Nat
      [Meta.synthInstance.instances] #[@instInhabitedOfMonad, instInhabitedNat]
  [Meta.synthInstance.apply] ✅️ apply instInhabitedNat to Inhabited Nat
    [Meta.synthInstance.tryResolve] ✅️ Inhabited Nat ≟ Inhabited Nat
    [Meta.synthInstance.answer] ✅️ Inhabited Nat
  [Meta.synthInstance.resume] ✅️ propagating Inhabited Nat to subgoal Inhabited Nat of Inhabited (Nat × Bool)
    [Meta.synthInstance.resume] size: 1
    [Meta.synthInstance] ✅️ new goal Inhabited Bool
      [Meta.synthInstance.instances] #[@instInhabitedOfMonad, instInhabitedBool]
  [Meta.synthInstance.apply] ✅️ apply instInhabitedBool to Inhabited Bool
    [Meta.synthInstance.tryResolve] ✅️ Inhabited Bool ≟ Inhabited Bool
    [Meta.synthInstance.answer] ✅️ Inhabited Bool
  [Meta.synthInstance.resume] ✅️ propagating Inhabited Bool to subgoal Inhabited Bool of Inhabited (Nat × Bool)
    [Meta.synthInstance.resume] size: 2
    [Meta.synthInstance.answer] ✅️ Inhabited (Nat × Bool)
  [Meta.synthInstance] result instInhabitedProd
-/
#guard_msgs in
set_option trace.Meta.synthInstance true in
store_traces_as myTrace in
example : Inhabited (Nat × Bool) := inferInstance

-- `#postprocess_traces` re-renders the stored trace through a postprocessor without re-running
-- the stored command.
/--
trace: [Meta.synthInstance.answer] ✅️ Inhabited Nat
[Meta.synthInstance.answer] ✅️ Inhabited Bool
[Meta.synthInstance.answer] ✅️ Inhabited (Nat × Bool)
-/
#guard_msgs in
#postprocess_traces myTrace hoist (ofClass `Meta.synthInstance.answer)

-- Postprocessors compose as in `postprocess_traces`.
/--
trace: [Meta.synthInstance] ✅️ Inhabited (Nat × Bool)
  [Meta.synthInstance.apply] ✅️ apply @instInhabitedProd to Inhabited (Nat × Bool)
    [Meta.synthInstance.tryResolve] ✅️ Inhabited (Nat × Bool) ≟ Inhabited (Nat × Bool)
  [Meta.synthInstance.apply] ✅️ apply instInhabitedNat to Inhabited Nat
    [Meta.synthInstance.tryResolve] ✅️ Inhabited Nat ≟ Inhabited Nat
  [Meta.synthInstance.apply] ✅️ apply instInhabitedBool to Inhabited Bool
    [Meta.synthInstance.tryResolve] ✅️ Inhabited Bool ≟ Inhabited Bool
-/
#guard_msgs in
#postprocess_traces myTrace filterSubtrees (ofClass `Meta.synthInstance.tryResolve)

/-- error: Unknown constant `notStored` -/
#guard_msgs in
#postprocess_traces notStored id

-- The stored trace is a real declaration of type `CoreM StoredTrace`, so arbitrary
-- metaprograms can inspect it.
/-- info: 1 -/
#guard_msgs in
#eval do return (← myTrace).trees.size

-- `StoredTrace.postprocess` applies a postprocessor programmatically.
/-- info: #["✅️ Inhabited Nat", "✅️ Inhabited Bool", "✅️ Inhabited (Nat × Bool)"] -/
#guard_msgs in
open Lean PostprocessTraces in
#eval show Lean.CoreM _ from do
  let t ← (← myTrace).postprocess (hoist (ofClass `Meta.synthInstance.answer))
  t.trees.mapM (·.headText)

-- Stored trace names live in the current namespace, like any other declaration.
namespace Nested
/--
trace: [Meta.synthInstance] ✅️ Inhabited Bool
  [Meta.synthInstance] ✅️ new goal Inhabited Bool
    [Meta.synthInstance.instances] #[@instInhabitedOfMonad, instInhabitedBool]
  [Meta.synthInstance.apply] ✅️ apply instInhabitedBool to Inhabited Bool
    [Meta.synthInstance.tryResolve] ✅️ Inhabited Bool ≟ Inhabited Bool
    [Meta.synthInstance.answer] ✅️ Inhabited Bool
  [Meta.synthInstance] result instInhabitedBool
-/
#guard_msgs in
set_option trace.Meta.synthInstance true in
store_traces_as inner in
example : Inhabited Bool := inferInstance
end Nested

/--
trace: [Meta.synthInstance] ✅️ Inhabited Bool
  [Meta.synthInstance] ✅️ new goal Inhabited Bool
    [Meta.synthInstance.instances] #[@instInhabitedOfMonad, instInhabitedBool]
  [Meta.synthInstance.apply] ✅️ apply instInhabitedBool to Inhabited Bool
    [Meta.synthInstance.tryResolve] ✅️ Inhabited Bool ≟ Inhabited Bool
    [Meta.synthInstance.answer] ✅️ Inhabited Bool
  [Meta.synthInstance] result instInhabitedBool
-/
#guard_msgs in
#postprocess_traces Nested.inner (filterSubtrees (fun _ => pure true))
