/-!
`simpArith` must simplify linear subterms nested inside *nonlinear* products.

The linear arithmetic simplifier treats nonlinear products as atoms. `Arith.parentIsTarget`
used to classify any `HMul` parent as a deferral target, assuming the simplifier would
normalize the child when processing the parent. For a nonlinear parent this never happens,
so e.g. the `+ 0` in `(x + 0) * y` was never simplified. See issue #13572, where such terms
reached `cutsat` and triggered a kernel type mismatch.

`simp +arith only` isolates `simpArith`: the default simp set (e.g. `Int.add_zero`) would
otherwise mask the behavior.
-/

/-! Linear subterm under a nonlinear product. -/

example (x y : Int) : (x + 0) * y = x * y := by
  simp +arith only

example (x y : Nat) : (x + 0) * y = x * y := by
  simp +arith only

example (x y : Int) : (x + 0) * (y + 0) = x * y := by
  simp +arith only

-- Nested: nonlinear product inside a linear (numeral-factor) product.
example (x y : Int) : 2 * ((x + 0) * y) = 2 * (x * y) := by
  simp +arith only

-- Cancellation inside a nonlinear product.
example (x y : Int) : (x + 1 - 1) * y = x * y := by
  simp +arith only

/-! Binary subtraction. -/

example (x y : Int) : (x - 0) * y = x * y := by
  simp +arith only

example (x y z : Int) : (x - (y + 0)) * z = (x - y) * z := by
  simp +arith only

-- Nat subtraction is not a linear term (truncated); it atomizes like a nonlinear product.
example (x y z : Nat) : (x - (y + 0)) * z = (x - y) * z := by
  simp +arith only

/-! Unary minus. -/

example (x y : Int) : (-(x + 0)) * y = (-x) * y := by
  simp +arith only

example (x y : Int) : -((x + 0) * y) = -(x * y) := by
  simp +arith only

/-! Division and modulo: `/` and `%` terms are atoms to the linear simplifier;
    linear subterms inside them must still be simplified. -/

example (x y : Int) : (x + 0) / y = x / y := by
  simp +arith only

example (x y : Int) : (x + 0) % y = x % y := by
  simp +arith only

example (x : Int) : (x + 0) / 2 = x / 2 := by
  simp +arith only

example (x : Int) : (x + 0) % 2 = x % 2 := by
  simp +arith only

example (x y z : Int) : ((x + 0) / (y + 0)) * z = (x / y) * z := by
  simp +arith only

example (x y : Nat) : (x + 0) / y = x / y := by
  simp +arith only

example (x y : Nat) : (x + 0) % y = x % y := by
  simp +arith only

-- `/` and `%` atoms inside a linear context.
example (x : Int) : (x / 2 + 0) + 1 = x / 2 + 1 := by
  simp +arith only

example (x : Int) : (x % 2 + 0) + 1 = x % 2 + 1 := by
  simp +arith only

/-! Controls: linear contexts. -/

example (x : Int) : (x + 0) + 1 = x + 1 := by
  simp +arith only

example (x : Int) : 2 * (x + 0) = 2 * x := by
  simp +arith only

example (x : Int) : (x + 0) * 2 = 2 * x := by
  simp +arith only

-- Negated numeral factor is still a linear mul.
example (x : Int) : (-2) * (x + 0) = -2 * x := by
  simp +arith only
