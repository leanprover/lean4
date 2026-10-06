/-!
Equations over commutative rings with a nonzero characteristic `c` (`Fin n`, `UInt8`, ...) in the
`Sym.simp`-based `grind` normalizer: when the leading coefficient is invertible modulo `c`, the
equation is solved for its monomial, as `2 * i = 6` becomes `i = 3` over `Int`.
-/
set_option warn.sorry false

section fin5
variable (x y : Fin 5)

example : (3 : Fin 5) + 4 = x := by grind_norm sym; guard_target = (x = 2); sorry
example : 4 * x + 2 = 0 := by grind_norm sym; guard_target = (x = 2); sorry
example : 3 * x + 1 = 0 := by grind_norm sym; guard_target = (x = 3); sorry
example : x + 3 = 0 := by grind_norm sym; guard_target = (x = 2); sorry
example : 3 * x = 0 := by grind_norm sym; guard_target = (x = 0); sorry
example : 2 * x = 2 * y := by grind_norm sym; guard_target = (x = y); sorry
example : 2 * x * y + 1 = 0 := by grind_norm sym; guard_target = (x * y = 2); sorry

-- Out-of-range numerals
example : (7 : Fin 5) = x := by grind_norm sym; guard_target = (2 = x); sorry
example : x = 7 := by grind_norm sym; guard_target = (x = 2); sorry

-- In-range equations between an atom and a numeral are kept as written.
example : (2 : Fin 5) = x := by grind_norm sym; guard_target = (2 = x); sorry
example : x = 2 := by grind_norm sym; guard_target = (x = 2); sorry

-- More than one monomial besides the `m₁ = m₂` shape: not solved.
example : 2 * x + 3 * y + 1 = 0 := by grind_norm sym; guard_target = (2 * x + 3 * y + 1 = 0); sorry

end fin5

section fin6
variable (x : Fin 6)

-- `2` is not invertible modulo `6`.
example : 2 * x + 1 = 0 := by grind_norm sym; guard_target = (2 * x + 1 = 0); sorry
example : 5 * x + 1 = 0 := by grind_norm sym; guard_target = (x = 1); sorry

end fin6

section uint8
variable (u : UInt8)

example : 3 * u = 1 := by grind_norm sym; guard_target = (u = 171); sorry
example : (200 : UInt8) + 100 = u := by grind_norm sym; guard_target = (u = 44); sorry
example : u = 300 := by grind_norm sym; guard_target = (u = 44); sorry
-- `2` is not invertible modulo `256`.
example : 2 * u = 4 := by grind_norm sym; guard_target = (2 * u + 252 = 0); sorry

end uint8
