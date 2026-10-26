/-!
Certificates by Kronecker substitution (`Grind.CommRing.Expr.eq_of_kron`) in `Sym.simp`'s
arithmetic normalizer: identities and normal forms over few variables are checked by evaluating
both sides at one point. Covers `=`, `≤`, `<`, commutative rings and semirings, large
coefficients, high powers, negative coefficients, a nonzero characteristic, linear terms over many
variables (`Expr.eq_of_kronLin`), relations whose sides differ by a constant, relations rewritten to
their normal form (`le_of_kron_rel`), and semiring relations whose common part is cancelled in the
certificate (`le_cancel_of_kronS`, `le_cancel_of_kronLinS`), and commutative semirings without
`AddRightCancel` (`Expr.eq_of_kronSN`). Each proof is checked by the kernel.
-/

set_option sym.arith.maxTerms 1000
set_option sym.arith.maxDegree 1000

register_sym_simp arithSimp where
  pre  := arith >> control >> arrow_telescope
  post := ground

example (a b c : Int) : (a - b + c)^5 = (a - b + c)^2 * (c - b + a)^3 := by sym => simp arithSimp
example (a b : Int) : (a + b)^40 = (a + b)^20 * (b + a)^20 := by sym => simp arithSimp
example (a b c : Int) : (1000 * a - 999 * b + c)^6 = ((1000 * a - 999 * b + c)^2)^3 := by sym => simp arithSimp
example (a b c : Int) : (a + b + c)^3 ≤ (a + b + c) * (a + b + c)^2 := by sym => simp arithSimp
example (a b c : Int) : ¬ (a + b + c)^3 < (a + b + c) * (a + b + c)^2 := by sym => simp arithSimp
example (a b c : Nat) : (a + 2 * b + c)^5 = (a + 2 * b + c)^2 * (a + 2 * b + c)^3 := by sym => simp arithSimp
example (a b : Nat) : (a + b)^30 ≤ (a + b)^10 * (a + b)^20 := by sym => simp arithSimp
example [Lean.Grind.CommRing α] (a b c : α) : (a + b + c)^4 = (a + b + c)^2 * (a + b + c)^2 := by sym => simp arithSimp
example [Lean.Grind.CommSemiring α] [Lean.Grind.AddRightCancel α] (a b c : α) :
    (a + b + c)^4 = (a + b + c)^2 * (a + b + c)^2 := by
  sym => simp arithSimp
example (x y : UInt64) : (x + 3 * y)^9 = (x + 3 * y)^4 * (x + 3 * y)^5 := by sym => simp arithSimp

-- Normal forms: the rewritten term is checked against the input.
example (f : Int → Int) (a b : Int) : f ((a - b)^4) = f (a^4 - 4*a^3*b + 6*a^2*b^2 - 4*a*b^3 + b^4) := by
  sym => simp arithSimp
example (f : Nat → Nat) (a b : Nat) : f ((a + b)^4) = f (a^4 + 4*a^3*b + 6*a^2*b^2 + 4*a*b^3 + b^4) := by
  sym => simp arithSimp

-- Linear terms over many variables.
example (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 : Int) : 1 * x0 + 2 * x1 + 3 * x2 + 4 * x3 + 5 * x4 + 1 * x5 + 2 * x6 + 3 * x7 + 4 * x8 + 5 * x9 + 1 * x10 + 2 * x11 + 3 * x12 + 4 * x13 + 5 * x14 + 1 * x15 + 2 * x16 + 3 * x17 + 4 * x18 + 5 * x19 + 1 * x20 + 2 * x21 + 3 * x22 + 4 * x23 + 5 * x24 + 1 * x25 + 2 * x26 + 3 * x27 + 4 * x28 + 5 * x29 + 1 * x30 + 2 * x31 + 3 * x32 + 4 * x33 + 5 * x34 + 1 * x35 + 2 * x36 + 3 * x37 + 4 * x38 + 5 * x39 = 5 * x39 + 4 * x38 + 3 * x37 + 2 * x36 + 1 * x35 + 5 * x34 + 4 * x33 + 3 * x32 + 2 * x31 + 1 * x30 + 5 * x29 + 4 * x28 + 3 * x27 + 2 * x26 + 1 * x25 + 5 * x24 + 4 * x23 + 3 * x22 + 2 * x21 + 1 * x20 + 5 * x19 + 4 * x18 + 3 * x17 + 2 * x16 + 1 * x15 + 5 * x14 + 4 * x13 + 3 * x12 + 2 * x11 + 1 * x10 + 5 * x9 + 4 * x8 + 3 * x7 + 2 * x6 + 1 * x5 + 5 * x4 + 4 * x3 + 3 * x2 + 2 * x1 + 1 * x0 := by sym => simp arithSimp
example (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 : Nat) : 1 * x0 + 2 * x1 + 3 * x2 + 4 * x3 + 5 * x4 + 1 * x5 + 2 * x6 + 3 * x7 + 4 * x8 + 5 * x9 + 1 * x10 + 2 * x11 + 3 * x12 + 4 * x13 + 5 * x14 + 1 * x15 + 2 * x16 + 3 * x17 + 4 * x18 + 5 * x19 + 1 * x20 + 2 * x21 + 3 * x22 + 4 * x23 + 5 * x24 + 1 * x25 + 2 * x26 + 3 * x27 + 4 * x28 + 5 * x29 + 1 * x30 + 2 * x31 + 3 * x32 + 4 * x33 + 5 * x34 + 1 * x35 + 2 * x36 + 3 * x37 + 4 * x38 + 5 * x39 ≤ 5 * x39 + 4 * x38 + 3 * x37 + 2 * x36 + 1 * x35 + 5 * x34 + 4 * x33 + 3 * x32 + 2 * x31 + 1 * x30 + 5 * x29 + 4 * x28 + 3 * x27 + 2 * x26 + 1 * x25 + 5 * x24 + 4 * x23 + 3 * x22 + 2 * x21 + 1 * x20 + 5 * x19 + 4 * x18 + 3 * x17 + 2 * x16 + 1 * x15 + 5 * x14 + 4 * x13 + 3 * x12 + 2 * x11 + 1 * x10 + 5 * x9 + 4 * x8 + 3 * x7 + 2 * x6 + 1 * x5 + 5 * x4 + 4 * x3 + 3 * x2 + 2 * x1 + 1 * x0 := by sym => simp arithSimp
example (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 : Int) : ¬ (1 * x0 + 2 * x1 + 3 * x2 + 4 * x3 + 5 * x4 + 1 * x5 + 2 * x6 + 3 * x7 + 4 * x8 + 5 * x9 + 1 * x10 + 2 * x11 + 3 * x12 + 4 * x13 + 5 * x14 + 1 * x15 + 2 * x16 + 3 * x17 + 4 * x18 + 5 * x19 + 1 * x20 + 2 * x21 + 3 * x22 + 4 * x23 + 5 * x24 + 1 * x25 + 2 * x26 + 3 * x27 + 4 * x28 + 5 * x29 + 1 * x30 + 2 * x31 + 3 * x32 + 4 * x33 + 5 * x34 + 1 * x35 + 2 * x36 + 3 * x37 + 4 * x38 + 5 * x39 < 5 * x39 + 4 * x38 + 3 * x37 + 2 * x36 + 1 * x35 + 5 * x34 + 4 * x33 + 3 * x32 + 2 * x31 + 1 * x30 + 5 * x29 + 4 * x28 + 3 * x27 + 2 * x26 + 1 * x25 + 5 * x24 + 4 * x23 + 3 * x22 + 2 * x21 + 1 * x20 + 5 * x19 + 4 * x18 + 3 * x17 + 2 * x16 + 1 * x15 + 5 * x14 + 4 * x13 + 3 * x12 + 2 * x11 + 1 * x10 + 5 * x9 + 4 * x8 + 3 * x7 + 2 * x6 + 1 * x5 + 5 * x4 + 4 * x3 + 3 * x2 + 2 * x1 + 1 * x0) := by sym => simp arithSimp

-- Relations whose sides differ by a constant.
example (a b c : Int) : ((a + b + c)^4 < (c + b + a)^4 + 1) = True := by sym => simp arithSimp
example (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 : Int) : (1 * x0 + 2 * x1 + 3 * x2 + 4 * x3 + 5 * x4 + 1 * x5 + 2 * x6 + 3 * x7 + 4 * x8 + 5 * x9 + 1 * x10 + 2 * x11 + 3 * x12 + 4 * x13 + 5 * x14 + 1 * x15 + 2 * x16 + 3 * x17 + 4 * x18 + 5 * x19 + 1 * x20 + 2 * x21 + 3 * x22 + 4 * x23 + 5 * x24 + 1 * x25 + 2 * x26 + 3 * x27 + 4 * x28 + 5 * x29 + 1 * x30 + 2 * x31 + 3 * x32 + 4 * x33 + 5 * x34 + 1 * x35 + 2 * x36 + 3 * x37 + 4 * x38 + 5 * x39 + 3 ≤ 5 * x39 + 4 * x38 + 3 * x37 + 2 * x36 + 1 * x35 + 5 * x34 + 4 * x33 + 3 * x32 + 2 * x31 + 1 * x30 + 5 * x29 + 4 * x28 + 3 * x27 + 2 * x26 + 1 * x25 + 5 * x24 + 4 * x23 + 3 * x22 + 2 * x21 + 1 * x20 + 5 * x19 + 4 * x18 + 3 * x17 + 2 * x16 + 1 * x15 + 5 * x14 + 4 * x13 + 3 * x12 + 2 * x11 + 1 * x10 + 5 * x9 + 4 * x8 + 3 * x7 + 2 * x6 + 1 * x5 + 5 * x4 + 4 * x3 + 3 * x2 + 2 * x1 + 1 * x0 + 2) = False := by sym => simp arithSimp
example (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 : Int) : (1 * x0 + 2 * x1 + 3 * x2 + 4 * x3 + 5 * x4 + 1 * x5 + 2 * x6 + 3 * x7 + 4 * x8 + 5 * x9 + 1 * x10 + 2 * x11 + 3 * x12 + 4 * x13 + 5 * x14 + 1 * x15 + 2 * x16 + 3 * x17 + 4 * x18 + 5 * x19 + 1 * x20 + 2 * x21 + 3 * x22 + 4 * x23 + 5 * x24 + 1 * x25 + 2 * x26 + 3 * x27 + 4 * x28 + 5 * x29 + 1 * x30 + 2 * x31 + 3 * x32 + 4 * x33 + 5 * x34 + 1 * x35 + 2 * x36 + 3 * x37 + 4 * x38 + 5 * x39 = 5 * x39 + 4 * x38 + 3 * x37 + 2 * x36 + 1 * x35 + 5 * x34 + 4 * x33 + 3 * x32 + 2 * x31 + 1 * x30 + 5 * x29 + 4 * x28 + 3 * x27 + 2 * x26 + 1 * x25 + 5 * x24 + 4 * x23 + 3 * x22 + 2 * x21 + 1 * x20 + 5 * x19 + 4 * x18 + 3 * x17 + 2 * x16 + 1 * x15 + 5 * x14 + 4 * x13 + 3 * x12 + 2 * x11 + 1 * x10 + 5 * x9 + 4 * x8 + 3 * x7 + 2 * x6 + 1 * x5 + 5 * x4 + 4 * x3 + 3 * x2 + 2 * x1 + 1 * x0 + 1) = False := by sym => simp arithSimp

-- Semiring terms with zero powers of high-degree terms (`Expr.degS_k`, `Expr.linS_k`).
example (x y : Nat) : (x^5 * y)^0 * (x + y) = y + x := by sym => simp arithSimp
example (x y : Nat) : (x * y)^0 * (x + 2 * y) + x = 2 * (x + y) := by sym => simp arithSimp
example (x y z : Nat) : (x^7)^0 * (x + y + z)^3 = (z + y + x)^2 * (x + y + z) := by sym => simp arithSimp

-- Relations rewritten to their normal form: `lhs - rhs` and `lhs' - rhs'` are checked at a point.
example (a b c d : Int) : ((a + b)^2 ≤ (c + d)^2) = (a^2 + 2*a*b + b^2 ≤ c^2 + 2*c*d + d^2) := by sym => simp arithSimp
example (a b c d e : Int) : ((a + b + c + d + e)^2 = 0) = ((e + d + c + b + a)^2 = 0) := by sym => simp arithSimp
example [Lean.Grind.CommRing α] [LE α] [LT α] [Std.IsPreorder α] [Std.LawfulOrderLT α] [Lean.Grind.OrderedRing α] (a b c : α) :
    ((a + b)^3 < c * (a - b)) = ((a + b)^3 < c * (a - b)) := by sym => simp arithSimp
-- Semiring relations with a common part: it is cancelled in the certificate.
example (a b c d : Nat) : ((a + b + c + d)^6 < (a + b + c + d)^2 * (a + b + c + d)^4 + 1) = ((d + c + b + a)^6 < (d + c + b + a)^6 + 1) := by
  sym => simp arithSimp
example (a b c : Nat) : ((a + b)^3 + 2 * c ≤ (b + a)^3 + c + 5) = (c ≤ 5) := by sym => simp arithSimp
example (a b c : Nat) : ((a + b)^3 + 2 * c = (b + a)^3 + c + 5) = (c = 5) := by sym => simp arithSimp
example (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 w : Nat) : (x0 + x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10 + x11 + x12 + x13 + x14 + x15 + x16 + x17 + x18 + x19 + x20 + x21 + x22 + x23 + x24 + x25 + x26 + x27 + x28 + x29 + x30 + x31 + x32 + x33 + x34 + x35 + x36 + x37 + x38 + x39 + 3 ≤ x39 + x38 + x37 + x36 + x35 + x34 + x33 + x32 + x31 + x30 + x29 + x28 + x27 + x26 + x25 + x24 + x23 + x22 + x21 + x20 + x19 + x18 + x17 + x16 + x15 + x14 + x13 + x12 + x11 + x10 + x9 + x8 + x7 + x6 + x5 + x4 + x3 + x2 + x1 + x0 + w) = (3 ≤ w) := by sym => simp arithSimp

-- Commutative semirings without `AddRightCancel`: the terms are regrouped in the semiring
-- (`Grind.CommRing.Expr.eq_of_kronSN`).
example [Lean.Grind.CommSemiring α] (a b c d : α) : (a + b + c + d)^6 = (a + b + c + d)^3 * (d + c + b + a)^3 := by
  sym => simp arithSimp
example [Lean.Grind.CommSemiring α] (a b : α) : (a + 2 * b)^3 = a^3 + 6 * a^2 * b + 12 * a * b^2 + 8 * b^3 := by
  sym => simp arithSimp
example [Lean.Grind.CommSemiring α] (f : α → α) (a b : α) : f ((a + b)^3) = f (b^3 + 3 * a * b^2 + 3 * a^2 * b + a^3) := by
  sym => simp arithSimp
