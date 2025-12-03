set_option warn.sorry false

axiom P : Nat → Prop
axiom aP n : P n

/-- trace: ⊢ P 0 -/
#guard_msgs in
example : P (Nat.ctorIdx Nat.zero) := by
  fail_if_success simp only []
  simp only [reduceCtorIdx]
  trace_state
  exact aP 0

/-- trace: ⊢ P 0 -/
#guard_msgs in
example : P (List.ctorIdx (List.nil : List Int)) := by
  fail_if_success simp only []
  simp only [reduceCtorIdx]
  trace_state
  exact aP 0

/-- trace: ⊢ P 1 -/
#guard_msgs in
example : P (List.ctorIdx [1,2,3]) := by
  fail_if_success simp only []
  simp only [reduceCtorIdx]
  trace_state
  exact aP 1

/-- trace: ⊢ P 1 -/
#guard_msgs in
example : P (Option.ctorIdx (.some true)) := by
  fail_if_success simp only []
  simp only [reduceCtorIdx]
  trace_state
  exact aP 1

/-- trace: ⊢ P 0 -/
#guard_msgs in
example : P (Option.ctorIdx (.none : Option Bool)) := by
  fail_if_success simp only []
  simp only [reduceCtorIdx]
  trace_state
  exact aP 0
