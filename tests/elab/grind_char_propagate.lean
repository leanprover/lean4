/-!
`grind` evaluates `Char.toNat`, `Char.val`, and `Char.ofNat` when their argument is known
to be a literal, via upward propagators: `y = 'a'` yields `y.toNat = 97` and `y.val = 97`,
and `n = 97` yields `Char.ofNat n = 'a'`.
-/

set_option grind.debug true

example (y : Char) : y = 'a' → y.toNat = 97 := by grind
example (y : Char) : y = Char.ofNat 97 → y.toNat = 97 := by grind
example (y : Char) : y = 'a' → y.val = 97 := by grind
example (y : Char) : y.toNat = 97 → y = 'a' → True := by grind
example (y : Char) (h : y.toNat ≠ 97) : y ≠ 'a' := by grind
example (y : Char) (h : y.val ≠ 97) : y ≠ 'a' := by grind
example (y : Char) (h : y = 'a' ∨ y = 'b') : y.toNat ≥ 97 := by grind
example (y : Char) (h : y = 'a' ∨ y = 'b') : y.toNat < 99 := by grind
example (f : Nat → Nat) (y : Char) : y = 'a' → f y.toNat = f 97 := by grind
example (n : Nat) (h : n = 97) : Char.ofNat n = 'a' := by grind
example (n : Nat) (h : n = 97) : (Char.ofNat n).toNat = 97 := by grind
example (n : Nat) (h : n = 0xd800) : Char.ofNat n = '\x00' := by grind
example (n : Nat) (h : n + 1 = 98) : Char.ofNat n = 'a' := by grind
example (n : Nat) (h : n = 97) (y : Char) (hy : y = 'b') : Char.ofNat n ≠ y := by grind
example (f : Char → Nat) (n : Nat) (h : n = 97) : f (Char.ofNat n) = f 'a' := by grind
example (s : List Char) (h : ∀ c ∈ s, c = 'a') : ∀ c ∈ s, c.toNat = 97 := by grind
