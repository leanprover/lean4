example [Add α] [Neg α] [Mul α] [∀ n, OfNat α n] {a b : α} :=
  calc
    4 + 5 * b = -6 + 5 * (b + 2) := sorry
            _ = -6 + 5 * 3 := sorry
