import Lean
/-!
Regression tests for the size bounds of the Kronecker certificates of `Sym.simp` and `grind`: their
parameters are estimated without building oversized integers, also under zero powers, rechecked when
two certificates share them, include the bases of zero powers, and are checked before `grind`
expands a characteristic quotient, whose size is bounded.
-/

register_sym_simp arithSimp where
  pre := arith >> control >> arrow_telescope
  post := ground

-- The coefficient estimate of `(x - x) ^ 64 ^ …` saturates instead of allocating billions of bits.
example (x : Int) : (((((((x - x)^64)^64)^64)^64)^64)^64) = 0 := by sym => simp arithSimp

-- A saturated estimate stays saturated under `^ 0`: the kernel still computes the estimate of the base.
example (x : Int) : ((((((((x - x)^64)^64)^64)^64)^64)^64)^0) = 1 := by sym => simp arithSimp

example [Lean.Grind.Field α] (x : α) : ((((((((x/2 - x/2)^64)^64)^64)^64)^64)^64)^0) = 1 := by
  sym => simp arithSimp

-- Semiring cancellation shares `K` and `B` between both sides and checks them together.
example (a b c d e f : Nat) : (a^64 + 1 ≤ f+e+d+c+b+1) = (a^64 ≤ b+c+d+e+f) := by
  sym => simp arithSimp

-- The kernel evaluates the base of a zero power, so its codes count.
example (a b c d e f g : Int) : a^64 + (b+c+d+e+f+g)^0 = a^64 + 1 := by
  sym => simp arithSimp

-- The bound rules out Kronecker substitution before the quotient by the characteristic is expanded.
set_option maxHeartbeats 20000 in
example [Lean.Grind.CommRing α] [Lean.Grind.IsCharP α 2] (a b c d e f g h : α) :
    ((((a + b + c + d + e + f + g + h)^2)^2)^2)^2 =
    a^16 + b^16 + c^16 + d^16 + e^16 + f^16 + g^16 + h^16 := by grind

-- Three terms in characteristic two, but 8385 over `Int`: the quotient is too large to state.
example [Lean.Grind.CommRing α] [Lean.Grind.IsCharP α 2] (x y : α) :
    (((((((x + y + 1)^2)^2)^2)^2)^2)^2)^2 = x^128 + y^128 + 1 := by
  grind

-- The linear certificate counts the codes of powers under `^ 0`, which the kernel evaluates.
set_option sym.arith.maxDegree 1000000000 in
example (x : Int) : (x^1000000000)^0 = 1 := by sym => simp arithSimp

-- Counting the terms of a power of a single term takes constant time.
set_option maxHeartbeats 20000 in
example [Lean.Grind.CommRing α] [Lean.Grind.IsCharP α 2] :
    (1 : α)^4000000000 = 1 := by grind (exp := 4000000000)
