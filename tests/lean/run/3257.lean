structure T : Prop
structure U : Prop

theorem foo : T → U := λ _ => {}
theorem bar : (_ : T := by trivial) → U := λ _ => {}

-- fails as expected
example : U := by
  fail_if_success simp
  sorry

-- works as expected, discharging `T` via `T.mk`
example : U := by
  simp [foo, T.mk]

example : U := by
  set_option trace.Meta.Tactic.simp true in
  simp [bar, T.mk]
