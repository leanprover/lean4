/-!
`Char.ofNat n` with an `OfNat` numeral `n` and the character literal `Char.ofNat (nat_lit n)`
are the same interpreted value. `grind` must canonicalize the former to the latter: otherwise
the two representations end up in one equivalence class as distinct interpreted nodes, and the
goal is closed with a proof the kernel rejects (`eq_false_of_decide`).
-/

set_option grind.debug true

example (y : Char) : y = Char.ofNat 97 → y = 'a' := by grind
example (y : Char) : y = Char.ofNat 97 → y ≠ 'b' := by grind
example (y : Char) : y = Char.ofNat 0 → y = '\x00' := by grind
example : Char.ofNat 97 = 'a' := by grind
example : Char.ofNat 97 ≠ 'b' := by grind
example (f : Char → Nat) : f (Char.ofNat 97) = f 'a' := by grind
example (f : Char → Nat) (h : f 'a' = 1) : f (Char.ofNat 97) = 1 := by grind
example (y : Char) (h : y ≠ 'a') : y ≠ Char.ofNat 97 := by grind
