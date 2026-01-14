/- More tactics -/

example (p q : Nat → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro h
  cases h with
  | intro x hpq =>
    cases hpq with
    | intro hp hq =>
      exists x

example : p ∧ q → q ∧ p := by
  intro p
  cases p
  constructor <;> assumption

example : p ∧ ¬ p → q := by
  intro h
  cases h
  contradiction
