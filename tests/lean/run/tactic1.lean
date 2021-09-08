theorem ex1 (x : Nat) (y : { v // v > x }) (z : Nat) : Nat :=
by {
  clear y x;
  exact z
}

theorem ex2 (x : Nat) (y : { v // v > x }) (z : Nat) : Nat :=
by {
  clear x y;
  exact z
}

theorem ex3 (x y z : Nat) (h₁ : x = y) (h₂ : z = y) : x = z :=
by {
  have : y = z := h₂.symm;
  apply Eq.trans;
  exact h₁;
  assumption
}

theorem ex4 (x y z : Nat) (h₁ : x = y) (h₂ : z = y) : x = z :=
by {
  let h₃ : y = z := h₂.symm;
  apply Eq.trans;
  exact h₁;
  exact h₃
}

theorem ex5 (x y z : Nat) (h₁ : x = y) (h₂ : z = y) : x = z :=
by {
  have h₃ : y = z := h₂.symm;
  apply Eq.trans;
  exact h₁;
  exact h₃
}

theorem ex6 (x y z : Nat) (h₁ : x = y) (h₂ : z = y) : id (x + 0 = z) :=
by {
  show x = z;
  have h₃ : y = z := h₂.symm;
  apply Eq.trans;
  exact h₁;
  exact h₃
}

theorem ex7 (x y z : Nat) (h₁ : x = y) (h₂ : z = y) : x = z := by
have : y = z := by apply Eq.symm; assumption
apply Eq.trans
exact h₁
assumption

theorem ex8 (x y z : Nat) (h₁ : x = y) (h₂ : z = y) : x = z :=
by apply Eq.trans h₁;
   have : y = z := by
     apply Eq.symm;
     assumption;
   exact this

example (x y z : Nat) (h₁ : x = y) (h₂ : z = y) : x = z := by
  sorry

example (x y z : Nat) (h₁ : x = y) (h₂ : z = y) : x = z := by
  apply Eq.trans
  . sorry
  . sorry
  . sorry

example (x y z : Nat) (h₁ : x = y) (h₂ : z = y) : x = z := by
  apply Eq.trans <;> sorry
