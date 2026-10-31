/-!
# Tests for the `arith` simproc on non-commutative rings and semirings

Monomials keep the order of their factors: `a * b` and `b * a` stay distinct, and
`(a + b)^2` expands to `a^2 + a*b + b*a + b^2`. Instances are local hypotheses.
-/

register_sym_simp arithSimp where
  pre  := arith >> control >> arrow_telescope
  post := ground

open Lean.Grind

section Ring
variable (R : Type u) [Ring R]

example (a b c : R) : a * (b - c) = - a * c + a * b := by
  sym => simp arithSimp

example (a b : R) : (a - b)^2 = a^2 - a * b - b * a + b^2 := by
  sym => simp arithSimp

example (a b : R) : (a + 2 * b)^2 = a^2 + 2 * a * b + 2 * b * a + 4 * b^2 := by
  sym => simp arithSimp

example (a b : R) : (a + 2 * b)^2 = a^2 + 2 * a * b + -b * (-4) * a - 2*b*a + 4 * b^2 := by
  sym => simp arithSimp

-- `a * b` and `b * a` are different monomials.
/-- error: `Sym.simp` made no progress -/
#guard_msgs in
example (a b : R) (h : a * b = b * a) : a * b = b * a := by
  sym =>
    simp arithSimp
    exact h

-- Relations.
example (a b c : R) (h : b * a = c) : a * b + b * a = a * b + c := by
  sym =>
    simp arithSimp
    exact h

example (a : R) : a * a * a = a ^ 3 := by
  sym => simp arithSimp

variable [IsCharP R 4]

example (a b : R) : (a - b)^2 = a^2 - a * b - b * 5 * a + b^2 := by
  sym => simp arithSimp

example (a b : R) : (a - b)^2 = 13*a^2 - a * b - b * 5 * a + b*3*b*3 := by
  sym => simp arithSimp
end Ring

section Semiring
variable (S : Type u) [Semiring S]

example (a b c : S) : a * (b + c) = a * c + a * b := by
  sym => simp arithSimp

example (a b : S) : (a + b)^2 = a^2 + a * b + b * a + b^2 := by
  sym => simp arithSimp

example (a b : S) : b^2 + (a + 2 * b)^2 = a^2 + 2 * a * b + b * (1+1) * a * 1 + 5 * b^2 := by
  sym => simp arithSimp

example (a b : S) : a^3 + a^2*b + a*b*a + b*a^2 + a*b^2 + b*a*b + b^2*a + b^3 = (a+b)^3 := by
  sym => simp arithSimp

-- Relations with cancellation of the common part need `AddRightCancel`.
example [AddRightCancel S] (a b : S) (h : a * b = b * a) : a * b + a = b * a + a := by
  sym =>
    simp arithSimp
    exact h

-- Without it, nothing can be cancelled and the relation is already normal.
/-- error: `Sym.simp` made no progress -/
#guard_msgs in
example (a b : S) (h : a * b = b * a) : a * b + a = b * a + a := by
  sym =>
    simp arithSimp
    exact congrArg (· + a) h
end Semiring
