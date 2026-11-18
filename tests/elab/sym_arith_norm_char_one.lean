/-!
Regression test for #16231: the `Sym.simp`-based arithmetic normalizer leaves structures of
characteristic `1` as written, whatever `maxChar` is. Their polynomials are not canonical
(`Poly.ofVar x` keeps the coefficient `1`), and the certificates built from them were rejected by
the kernel. `grind`'s ring solver handles these structures directly.
-/
set_option warn.sorry false

register_sym_simp arithSimp where
  pre := arith

def R := Fin 1
instance : Lean.Grind.Ring R := inferInstanceAs (Lean.Grind.Ring (Fin 1))
instance : Lean.Grind.IsCharP R 1 := inferInstanceAs (Lean.Grind.IsCharP (Fin 1) 1)

def S := Fin 1
instance : Lean.Grind.CommSemiring S := inferInstanceAs (Lean.Grind.CommSemiring (Fin 1))
instance : Lean.Grind.IsCharP S 1 := inferInstanceAs (Lean.Grind.IsCharP (Fin 1) 1)
instance : Lean.Grind.AddRightCancel S := ⟨fun a b _ _ => Subsingleton.elim (α := Fin 1) a b⟩

section grind
set_option backward.grind.normalizer false

example (x : Fin 1) : (0 : Fin 1) = x ^ 2 := by grind (maxChar := 1)
example (x : BitVec 0) : (0 : BitVec 0) = x ^ 2 := by grind (maxChar := 1)
example (x y : Fin 1) : x * y = x ^ 2 := by grind (maxChar := 1)
example (x y : Fin 1) : x ^ 0 = y := by grind (maxChar := 1)
example (x : Fin 1) : (1 : Fin 1) = x ^ 3 + x := by grind (maxChar := 1)
example (x y : Fin 1) (f : Fin 1 → Nat) : f (x ^ 2) = f (x * y + 2) := by grind (maxChar := 1)
example (x y : R) : x * y = y * x ^ 2 := by grind (maxChar := 1)
example (x y : S) : x * y = y * x ^ 2 + 1 := by grind (maxChar := 1)

end grind

section norm
variable (x y : Fin 1) (f : Fin 1 → Nat)

example : (0 : Fin 1) = x ^ 2 := by grind_norm (maxChar := 1) sym; guard_target = ((0 : Fin 1) = x ^ 2); sorry
example : x * y = x ^ 2 := by grind_norm (maxChar := 1) sym; guard_target = (x * y = x ^ 2); sorry
example : x - y = y * x := by grind_norm (maxChar := 1) sym; guard_target = (x - y = y * x); sorry
example : f (x ^ 0) = f (x - y) := by grind_norm (maxChar := 1) sym; guard_target = (f (x ^ 0) = f (x - y)); sorry
example (a b : R) : a * b = b * a ^ 2 := by grind_norm (maxChar := 1) sym; guard_target = (a * b = b * a ^ 2); sorry
example (a b : S) : a * b = b * a ^ 2 + 1 := by grind_norm (maxChar := 1) sym; guard_target = (a * b = b * a ^ 2 + 1); sorry

-- Without `maxChar`.
example : (0 : Fin 1) = x ^ 2 := by
  fail_if_success sym => simp arithSimp
  sorry
example : x * y = x ^ 2 := by
  fail_if_success sym => simp arithSimp
  sorry
example (a b : R) : a * b = b * a ^ 2 := by
  fail_if_success sym => simp arithSimp
  sorry
example (a b : S) : a * b = b * a ^ 2 := by
  fail_if_success sym => simp arithSimp
  sorry

end norm
