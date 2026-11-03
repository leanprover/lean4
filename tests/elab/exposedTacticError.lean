module

/-! A failing `by` block in an exposed definition must not also cause a kernel error about
metavariables, and the definition must still be usable afterwards. -/

public structure S where
  n : Nat
  h : n = n

/-- error: boom
⊢ 0 = 0 -/
#guard_msgs in
@[expose] public def exposedFail : S := ⟨0, by fail "boom"⟩

/-- error: No goals to be solved -/
#guard_msgs in
@[expose] public def exposedNoGoals : S := ⟨0, by simp; omega⟩

#guard_msgs in
public theorem usesExposedFail : exposedFail.n = 0 := rfl
