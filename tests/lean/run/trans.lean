instance : Trans (α := Nat) (β := Nat) (γ := Nat) (.≤.) (.≤.) (.≤.) where
  trans := Nat.le_trans

instance : Trans (α := Int) (β := Int) (γ := Int) (.≤.) (.≤.) (.≤.) where
  trans := sorry

theorem ex1 {a b c d : Nat} (h1 : a ≤ b) (h2 : b ≤ c) (h3 : c ≤ d) : a ≤ d :=
  trans h1 <| trans h2 h3

theorem ex2 {a b c d : Int} (h1 : a ≤ b) (h2 : b ≤ c) (h3 : c ≤ d) : a ≤ d :=
  trans h1 <| trans h2 h3
