import Lean

/-!
Tests for trace postprocessors: the `trace_view post in cmd` command, the basic combinators in
`Lean.TraceView`, and the stored-trace commands `store_trace_as`, `#trace_roots`, `#trace_view`.
-/

-- `hideSucceeded` folds a fully successful trace into its root line.
/-- trace: [Meta.synthInstance] ✅️ Inhabited (List Nat) -/
#guard_msgs in
set_option trace.Meta.synthInstance true in
trace_view hideSucceeded in
example : Inhabited (List Nat) := inferInstance

-- `focusOn` hoists matching subtrees to the top level.
/-- trace: [Meta.synthInstance.instances] #[@instInhabitedOfMonad, @instInhabitedList] -/
#guard_msgs in
set_option trace.Meta.synthInstance true in
trace_view focusOn `Meta.synthInstance.instances in
example : Inhabited (List Nat) := inferInstance

-- `grep` keeps matching subtrees (here: by trace class) plus their ancestors for context.
/--
trace: [Meta.synthInstance] ✅️ Inhabited (List Nat)
  [Meta.synthInstance.apply] ✅️ apply @instInhabitedList to Inhabited (List Nat)
    [Meta.synthInstance.tryResolve] ✅️ Inhabited (List Nat) ≟ Inhabited (List Nat)
-/
#guard_msgs in
set_option trace.Meta.synthInstance true in
trace_view grep "tryResolve" in
example : Inhabited (List Nat) := inferInstance

-- Postprocessors compose left-to-right with `>=>`.
/--
trace: [Meta.synthInstance] ✅️ Inhabited (List Nat)
  [Meta.synthInstance] result instInhabitedList
-/
#guard_msgs in
set_option trace.Meta.synthInstance true in
trace_view maxDepth 1 >=> grep "result" in
example : Inhabited (List Nat) := inferInstance

-- A postprocessor returning no roots drops the trace message entirely.
#guard_msgs in
set_option trace.Meta.synthInstance true in
trace_view (fun _ => return #[]) in
example : Inhabited (List Nat) := inferInstance

-- User-defined postprocessor: keep only the `apply` steps directly below each root.
open Lean TraceView in
def onlyApplies : TracePostprocessor := fun roots =>
  return roots.map fun r =>
    r.withChildren (r.children.filter (·.cls? == some `Meta.synthInstance.apply))

/--
trace: [Meta.synthInstance] ✅️ Inhabited (List Nat)
  [Meta.synthInstance.apply] ✅️ apply @instInhabitedList to Inhabited (List Nat)
    [Meta.synthInstance.tryResolve] ✅️ Inhabited (List Nat) ≟ Inhabited (List Nat)
    [Meta.synthInstance.answer] ✅️ Inhabited (List Nat)
-/
#guard_msgs in
set_option trace.Meta.synthInstance true in
trace_view onlyApplies in
example : Inhabited (List Nat) := inferInstance

-- `store_trace_as` reports the trace unchanged and stores it for later inspection.
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
store_trace_as myTrace in
example : Inhabited (Nat × Bool) := inferInstance

-- `#trace_roots` lists the stored roots with index, class, position, and size.
/-- info: #0 [Meta.synthInstance] 93:36 (21 nodes) ✅️ Inhabited (Nat × Bool) -/
#guard_msgs in
#trace_roots myTrace

-- `#trace_view` re-renders the stored trace through a postprocessor without re-running the
-- stored command.
/-- trace: [Meta.synthInstance] ✅️ Inhabited (Nat × Bool) -/
#guard_msgs in
#trace_view myTrace maxDepth 0

-- `onRootIdx` restricts a postprocessor to the root with the given (stable) index.
/--
trace: [Meta.synthInstance.answer] ✅️ Inhabited Nat
[Meta.synthInstance.answer] ✅️ Inhabited Bool
[Meta.synthInstance.answer] ✅️ Inhabited (Nat × Bool)
-/
#guard_msgs in
#trace_view myTrace onRootIdx 0 (focusOn `Meta.synthInstance.answer)

/--
error: unknown stored trace `notStored` (stored traces: `myTrace`); store one using `store_trace_as notStored in <command>`
-/
#guard_msgs in
#trace_roots notStored
