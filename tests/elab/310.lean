variable (xs : List Nat)

theorem foo1 : xs = xs := by
  induction xs <;> rfl

theorem foo2 : xs = xs := by
  cases xs with
  | nil        => rfl
  | cons x xs  => rfl
