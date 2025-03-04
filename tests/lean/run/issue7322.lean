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
