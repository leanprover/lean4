theorem bad : ∀ (m n : Nat), (if m = n then Ordering.eq else Ordering.gt) = Ordering.lt → False := by
  intros m n
  cases (Nat.decEq m n) with -- an error as expected: "Alternative `isFalse` has not bee provided"
  | isTrue h =>
    set_option trace.Meta.Tactic.simp.rewrite true in
    simp [h]

theorem bad' : ∀ (m n : Nat), (if m = n then Ordering.eq else Ordering.gt) = Ordering.lt → False := by
  intros m n
  cases (Nat.decEq m n) with
  | isTrue h =>
    simp [h]
  | isFalse h =>
    simp [h]
