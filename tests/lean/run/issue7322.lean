-- set_option trace.Elab.definition.fixedParams true in
-- set_option debug.skipKernelTC true
-- set_option debug.definition.wf.replaceRecApps true
-- set_option trace.Elab.definition.wf true
set_option pp.proofs true

/-!
This test case show a tricky issue, originally shown in
`Std.Tactic.BVDecide.BVExpr.bitblast.blastShiftLeftConst.go_denote_eq`
where type of `fix`’s induction hypothese change when being refined
in a way that makes the resulting proof term type incorrect.
-/

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
theorem demo (distance : Nat) (idx : Nat) (a : Fin distance) (fuel : Nat) :
    a = if hidx : idx < distance then Fin.mk idx hidx else a := by
  cases fuel
  · sorry
  next fuel =>
    split
    · rw [demo distance idx a fuel]
      sorry
    · rfl
termination_by fuel
decreasing_by sorry

structure Ev (p : Prop) : Type where
  isTrue : p

/--
warning: declaration uses 'sorry'
---
warning: declaration uses 'sorry'
---
warning: declaration uses 'sorry'
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
def bar (distance : Nat) (idx : Nat) (a : Fin distance) (fuel : Nat) :
    Ev (a = if hidx : idx < distance then Fin.mk idx hidx else a) := by
  cases fuel
  · sorry
  next fuel =>
    split
    · rw [(bar distance idx a fuel).isTrue]
      sorry
    · apply Ev.mk
      rfl
termination_by fuel
decreasing_by sorry

set_option Elab.async false -- for stable message ordering in guard_msgs

/--
warning: declaration uses 'sorry'
---
info: bar.induct (motive : Nat → Prop) (case1 : ∀ (x : Nat), (∀ (n : Nat), motive n) → motive x) (fuel : Nat) : motive fuel
-/
#guard_msgs in
#check bar.induct
