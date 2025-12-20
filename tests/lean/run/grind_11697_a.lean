namespace Nat

@[grind =]
theorem testBit_shiftRight_shiftLeft_add {n j k : Nat} (x : Nat) : (x >>> n <<< (n + k)).testBit j =
    (decide (n + k ≤ j) && x.testBit (j - k)) := by
  grind

theorem myTheorem {x : Nat} : x = x := by grind

end Nat
