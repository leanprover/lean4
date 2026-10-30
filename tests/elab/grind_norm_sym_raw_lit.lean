/-!
`Sym.simp` must fold an orphan raw `Nat` literal into the `OfNat.ofNat` numeral form, as
`Meta.simp` does. The `[grind hom]` rule `Fin.val_OfNat_ofNat : (OfNat.ofNat a : Fin n).val = a % n`
binds `a` to the raw literal inside the `Fin` numeral, so its output `nat_lit 0 % (p + 1)` was
not recognized as a numeral by any later step (`Nat.zero_mod`, cutsat), and the goals below
failed with the `Sym.simp`-based normalizer.
-/

set_option backward.grind.normalizer false

example (p : Nat) (heq : p = 1) (n : Fin (p + 1)) : n = 0 ∨ n = 1 := by grind
example (p d : Nat) (n : Fin (p + 1)) : 2 ≤ p → p ≤ d + 1 → d = 1 → n = 0 ∨ n = 1 ∨ n = 2 := by grind
example {n m : Nat} (x : BitVec n) : 2 ≤ n → n ≤ m → m = 2 → x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by grind

set_option warn.sorry false

#guard_msgs in
example (p : Nat) : (nat_lit 0) % (p + 1) = p := by grind_norm check; sorry

#guard_msgs in
example (p : Nat) (f : Nat → Nat) : f (nat_lit 2) = p := by grind_norm check; sorry

-- The raw literal of a numeral stays raw.
#guard_msgs in
example (p : Nat) (x : Fin 5) : x = (3 : Fin 5) := by grind_norm check; sorry

#guard_msgs in
example (c : Char) : c = 'a' := by grind_norm check; sorry
