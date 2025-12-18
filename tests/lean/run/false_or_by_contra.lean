example (w : False) : False := by
  false_or_by_contra
  guard_target = False
  exact w

example : False → Nat := by
  false_or_by_contra <;> rename_i h
  guard_target = False
  guard_hyp h : False
  simp_all

example {P : Prop} (p : P) : Nat → Nat → P := by
  false_or_by_contra <;> rename_i a b h
  guard_target = False
  guard_hyp a : Nat
  guard_hyp b : Nat
  guard_hyp h : ¬ P
  simp_all

example {P : Prop} : False → P := by
  false_or_by_contra <;> rename_i h w
  guard_target = False
  guard_hyp h : False
  guard_hyp w : ¬ P
  simp_all

example (_ : False) : x ≠ y := by
  false_or_by_contra <;> rename_i h
  guard_hyp h : x = y
  guard_target = False
  simp_all

example (_ : False) : ¬ P := by
  false_or_by_contra <;> rename_i h
  guard_hyp h : P
  guard_target = False
  simp_all

example {P : Prop} (_ : False) : P := by
  false_or_by_contra <;> rename_i h
  guard_hyp h : ¬ P
  guard_target = False
  simp_all

-- It doesn't make sense to use contradiction if the goal is a Type (rather than a Prop).
example {P : Type} (_ : False) : P := by
  false_or_by_contra
  fail_if_success
    have : ¬ P := by assumption
  guard_target = False
  simp_all
