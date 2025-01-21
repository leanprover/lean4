set_option grind.debug true

example (p q : Prop) (a b c d : Nat) :
     a = b → c = d → a ≠ c → (d ≠ b → p) → (d ≠ b → q) → p ∧ q := by
  grind (splits:=0)
