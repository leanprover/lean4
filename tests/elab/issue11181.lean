set_option warn.sorry false


theorem Nat.foo₁ (n : Nat) : n ^^^ 0 = n ^^^ 0 := by
  cases n
  · simp only [HXor.hXor, instXorOp, xor, bitwise, Bool.bne_true, Bool.not_false, ↓reduceIte]
  · sorry

theorem Nat.foo₂ : 0 ^^^ 0 = 0 ^^^ 0 := by
  simp only [HXor.hXor, instXorOp, xor, bitwise, Bool.bne_true, Bool.not_false, ↓reduceIte]
