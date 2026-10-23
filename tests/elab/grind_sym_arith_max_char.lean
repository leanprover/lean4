/-!
`Grind.Config.maxChar`: the `Sym.simp`-based `grind` normalizer leaves arithmetic over a type
with a nonzero characteristic above `maxChar` (default `0`), or with a symbolic characteristic,
as written. Over `BitVec 64` the ring normal form would turn `p - a` into
`p + 18446744073709551615 * a`, which hides the subtraction from `[grind =]` rules and from the
`[grind hom]` translation into `Nat`.

`backward.grind.normalizer` is set per example: set for the whole file, it also selects the
normalizer used for E-matching patterns at attribute time, and `grind_norm check` compares the
`Sym.simp` normalizer with itself.
-/
set_option warn.sorry false

opaque f : BitVec 64 → Nat
opaque g : BitVec 64 → BitVec 64 → Nat
@[grind =] theorem f_sub (p a : BitVec 64) : f (p - a) = g p a := sorry

set_option backward.grind.normalizer false in
example (p a : BitVec 64) : f (p - a) = g p a := by grind

-- Both normalizers leave these as written.
example (x y : BitVec 64) : (x - y).toNat = 3 := by grind_norm check; sorry
example (x y : BitVec 64) : x - y = 3 := by grind_norm check; sorry
example (x y : UInt8) : x - y = 3 := by grind_norm check; sorry
example (n : Nat) [NeZero n] (x y : Fin n) : x - y = 3 := by grind_norm check; sorry
example (w : Nat) (x y : BitVec w) : x - y = 3 := by grind_norm check; sorry
example (x : Int8) : (100 : Int8) + 100 = x := by grind_norm check; sorry

-- Casts of numerals are still rewritten to the numeral of the carrier.
section
attribute [local instance] Lean.Grind.Semiring.natCast
set_option backward.grind.normalizer false in
example (h : UInt8 → UInt8) : h ↑(3 : Nat) = h 3 := by grind
set_option backward.grind.normalizer false in
example (h : Fin 2 → Fin 2) : h ↑(3 : Nat) = h 1 := by grind
end

-- Characteristic zero is unaffected.
example (x y : Int) : x - y = 3 := by grind_norm sym; guard_target = (x + -1 * y + -3 = 0); sorry

-- With a large enough `maxChar`, the ring normal form is used.
example (x : Fin 5) : 3 * x + 1 = 0 := by grind_norm (maxChar := 5) sym; guard_target = (x = 3); sorry
example (x : Fin 5) : 3 * x + 1 = 0 := by grind_norm sym; guard_target = (3 * x + 1 = 0); sorry
example (x y : BitVec 64) : x - y = 3 := by
  grind_norm (maxChar := 2^64) sym; guard_target = (x + 18446744073709551615 * y + 18446744073709551613 = 0); sorry
set_option backward.grind.normalizer false in
example (a b c : UInt32) : a ≤ 2 → b ≤ 3 → -1 * a + -1 * b + c = 0 → c ≤ 5 := by grind
set_option backward.grind.normalizer false in
example (a b c : UInt32) : a ≤ 2 → b ≤ 3 → -1 * a + -1 * b + c = 0 → c ≤ 5 := by grind (maxChar := 2^32)
