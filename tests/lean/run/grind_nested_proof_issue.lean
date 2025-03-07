example (as bs : Array α) (v : α)
        (i : Nat)
        (h₁ : i < as.size)
        (h₂ : bs = as.set i v)
        : (as.set i v).size = as.size → as.size = bs.size := by
  grind
