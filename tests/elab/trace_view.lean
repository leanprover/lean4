import Lean

/-!
Tests for trace postprocessors: the `trace_view post in cmd` command, the basic combinators in
`Lean.TraceView`, and the stored-trace commands `store_trace_as`, `#trace_roots`, `#trace_view`.
-/

open scoped Lean.TraceView

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

/-!
`expandMatches` only changes `TraceData.collapsed` flags, which are invisible in textual
output, so we test the flags directly on a synthetic tree.
-/

open Lean TraceView in
private def mkTree (cls : Name) (msg : String) (kids : Array TraceTree := #[])
    (collapsed := true) : TraceTree :=
  .node { cls, collapsed } m!"{msg}" kids id

open Lean TraceView in
private partial def collapsedFlags (t : TraceTree) : String :=
  let state := if (t.data?.map (·.collapsed)).getD true then "closed" else "open"
  let head := s!"{t.cls?.getD .anonymous}:{state}"
  if t.children.isEmpty then head
  else head ++ "[" ++ ",".intercalate (t.children.map collapsedFlags).toList ++ "]"

open Lean TraceView in
private def sampleTree : TraceTree :=
  mkTree `a "root" #[
    mkTree `b "mid" #[mkTree `c "the needle is here"],
    mkTree `d "other branch" #[mkTree `zeta "leaf"] (collapsed := false)
  ]

-- The parents of the message match open; the match itself stays closed, and the unrelated
-- node `d` keeps its (open) expansion state.
/-- info: "a:open[b:open[c:closed],d:open[zeta:closed]]" -/
#guard_msgs in
open Lean.TraceView in
#eval show Lean.CoreM _ from do
  return collapsedFlags (← expandMatches "needle" #[sampleTree])[0]!

-- Matching by trace class works too.
/-- info: "a:open[b:closed[c:closed],d:open[zeta:closed]]" -/
#guard_msgs in
open Lean.TraceView in
#eval show Lean.CoreM _ from do
  return collapsedFlags (← expandMatches "zeta" #[sampleTree])[0]!

-- Without a match, all expansion states are unchanged.
/-- info: "a:closed[b:closed[c:closed],d:open[zeta:closed]]" -/
#guard_msgs in
open Lean.TraceView in
#eval show Lean.CoreM _ from do
  return collapsedFlags (← expandMatches "no such text" #[sampleTree])[0]!
