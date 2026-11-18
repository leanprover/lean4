/-!
Benchmarks for the `arith` simproc of `Sym.simp` (`Sym.Arith.normalize?`): elaboration of the
polynomial normal form and kernel checking of its certificates, on long sums, large expansions,
shared subterms, fields, nonzero characteristic, `Nat`, relations and many small goals.
-/

register_sym_simp arithSimp where
  pre  := arith >> control >> arrow_telescope
  post := ground

-- A long linear sum, permuted.
example (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 : Int) :
    1 * x0 + 2 * x1 + 3 * x2 + 4 * x3 + 5 * x4 + 6 * x5 + 7 * x6 + 1 * x7 + 2 * x8 + 3 * x9 + 4 * x10 + 5 * x11 + 6 * x12 + 7 * x13 + 1 * x14 + 2 * x15 + 3 * x16 + 4 * x17 + 5 * x18 + 6 * x19 + 7 * x20 + 1 * x21 + 2 * x22 + 3 * x23 + 4 * x24 + 5 * x25 + 6 * x26 + 7 * x27 + 1 * x28 + 2 * x29 + 3 * x30 + 4 * x31 + 5 * x32 + 6 * x33 + 7 * x34 + 1 * x35 + 2 * x36 + 3 * x37 + 4 * x38 + 5 * x39 =
    5 * x39 + 4 * x38 + 3 * x37 + 2 * x36 + 1 * x35 + 7 * x34 + 6 * x33 + 5 * x32 + 4 * x31 + 3 * x30 + 2 * x29 + 1 * x28 + 7 * x27 + 6 * x26 + 5 * x25 + 4 * x24 + 3 * x23 + 2 * x22 + 1 * x21 + 7 * x20 + 6 * x19 + 5 * x18 + 4 * x17 + 3 * x16 + 2 * x15 + 1 * x14 + 7 * x13 + 6 * x12 + 5 * x11 + 4 * x10 + 3 * x9 + 2 * x8 + 1 * x7 + 7 * x6 + 6 * x5 + 5 * x4 + 4 * x3 + 3 * x2 + 2 * x1 + 1 * x0 := by sym => simp arithSimp

-- Collecting like terms in a long sum.
example (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 : Int) :
    (x0 + x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10 + x11 + x12 + x13 + x14 + x15 + x16 + x17 + x18 + x19 + x20 + x21 + x22 + x23 + x24 + x25 + x26 + x27 + x28 + x29 + x30 + x31 + x32 + x33 + x34 + x35 + x36 + x37 + x38 + x39) + (x0 + x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10 + x11 + x12 + x13 + x14 + x15 + x16 + x17 + x18 + x19 + x20 + x21 + x22 + x23 + x24 + x25 + x26 + x27 + x28 + x29 + x30 + x31 + x32 + x33 + x34 + x35 + x36 + x37 + x38 + x39) = 2 * (x0 + x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10 + x11 + x12 + x13 + x14 + x15 + x16 + x17 + x18 + x19 + x20 + x21 + x22 + x23 + x24 + x25 + x26 + x27 + x28 + x29 + x30 + x31 + x32 + x33 + x34 + x35 + x36 + x37 + x38 + x39) := by sym => simp arithSimp

example (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 : Nat) :
    1 * x0 + 2 * x1 + 3 * x2 + 4 * x3 + 5 * x4 + 6 * x5 + 7 * x6 + 1 * x7 + 2 * x8 + 3 * x9 + 4 * x10 + 5 * x11 + 6 * x12 + 7 * x13 + 1 * x14 + 2 * x15 + 3 * x16 + 4 * x17 + 5 * x18 + 6 * x19 + 7 * x20 + 1 * x21 + 2 * x22 + 3 * x23 + 4 * x24 + 5 * x25 + 6 * x26 + 7 * x27 + 1 * x28 + 2 * x29 + 3 * x30 + 4 * x31 + 5 * x32 + 6 * x33 + 7 * x34 + 1 * x35 + 2 * x36 + 3 * x37 + 4 * x38 + 5 * x39 =
    5 * x39 + 4 * x38 + 3 * x37 + 2 * x36 + 1 * x35 + 7 * x34 + 6 * x33 + 5 * x32 + 4 * x31 + 3 * x30 + 2 * x29 + 1 * x28 + 7 * x27 + 6 * x26 + 5 * x25 + 4 * x24 + 3 * x23 + 2 * x22 + 1 * x21 + 7 * x20 + 6 * x19 + 5 * x18 + 4 * x17 + 3 * x16 + 2 * x15 + 1 * x14 + 7 * x13 + 6 * x12 + 5 * x11 + 4 * x10 + 3 * x9 + 2 * x8 + 1 * x7 + 7 * x6 + 6 * x5 + 5 * x4 + 4 * x3 + 3 * x2 + 2 * x1 + 1 * x0 := by sym => simp arithSimp

-- Expansions.
example (a b c d : Int) : (a + b + c + d)^4 = (a + b + c + d)^2 * (a + b + c + d)^2 := by sym => simp arithSimp
example (a b : Int) : (a + b)^12 = (a + b)^6 * (a + b)^6 := by sym => simp arithSimp
example (x y z : Int) : (x - y)^3 * (y - z)^3 * (z - x)^3 = ((x - y) * (y - z) * (z - x))^3 := by sym => simp arithSimp
example [Lean.Grind.CommRing α] (a b c d : α) : (a + b + c + d)^4 = (a + b + c + d)^2 * (a + b + c + d)^2 := by sym => simp arithSimp
example (a b c d : Nat) : (a + b + c + d)^4 = (a + b + c + d)^2 * (a + b + c + d)^2 := by sym => simp arithSimp
example (a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : Int) :
    (a₁^2 + a₂^2 + a₃^2 + a₄^2) * (b₁^2 + b₂^2 + b₃^2 + b₄^2) =
      (a₁*b₁ - a₂*b₂ - a₃*b₃ - a₄*b₄)^2 + (a₁*b₂ + a₂*b₁ + a₃*b₄ - a₄*b₃)^2 +
      (a₁*b₃ - a₂*b₄ + a₃*b₁ + a₄*b₂)^2 + (a₁*b₄ + a₂*b₃ - a₃*b₂ + a₄*b₁)^2 := by sym => simp arithSimp

-- Shared subterms: `t` occurs many times.
example (a b c : Int) :
    let t := (a + b + c)^2
    t * t + t * t + t * t = 3 * (t * t) := by intros; sym => simp arithSimp

-- Fields.
example (a b c d : Rat) : a / 2 + b / 3 + c / 5 + d / 7 = (105 * a + 70 * b + 42 * c + 30 * d) / 210 := by sym => simp arithSimp
example (a b c : Rat) : (a + b) / c + (b + c) / a = a * c⁻¹ + b * c⁻¹ + b * a⁻¹ + c * a⁻¹ := by sym => simp arithSimp
example (x y : Rat) : (x / 3 + y / 4)^4 = (4 * x + 3 * y)^4 / 20736 := by sym => simp arithSimp

-- Nonzero characteristic.
example (x y : UInt8) : (x + y)^8 = (x + y)^4 * (x + y)^4 := by sym => simp arithSimp
example (x y z : BitVec 16) : (x + 3 * y + 5 * z)^4 = ((x + 3 * y + 5 * z)^2)^2 := by sym => simp arithSimp
example (x y : Fin 13) : (x + y)^13 = (x + y)^6 * (x + y)^7 := by sym => simp arithSimp

-- Relations.
example (a b c d : Int) : ((a + b)^2 ≤ (c + d)^2) = (a^2 + 2*a*b + b^2 ≤ c^2 + 2*c*d + d^2) := by sym => simp arithSimp
example (a b c : Int) : (2 * (a + b + c) < 4 * (a - b) + 6 * c) = (6 * b < 2 * a + 4 * c) := by sym => simp arithSimp
example (x y : Rat) : (x / 2 + y / 3 = 1) = (3 * x + 2 * y = 6) := by sym => simp arithSimp
example (a b c d e : Int) : ((a + b + c + d + e)^2 = 0) = ((e + d + c + b + a)^2 = 0) := by sym => simp arithSimp

example (a b c : Int) : (a + 2 * b) * (c - 0) = a * c - 0 * a + 2 * b * c - 0 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 3 * b) * (c - 1) = a * c - 1 * a + 3 * b * c - 3 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 4 * b) * (c - 2) = a * c - 2 * a + 4 * b * c - 8 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 5 * b) * (c - 3) = a * c - 3 * a + 5 * b * c - 15 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 6 * b) * (c - 4) = a * c - 4 * a + 6 * b * c - 24 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 2 * b) * (c - 5) = a * c - 5 * a + 2 * b * c - 10 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 3 * b) * (c - 6) = a * c - 6 * a + 3 * b * c - 18 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 4 * b) * (c - 7) = a * c - 7 * a + 4 * b * c - 28 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 5 * b) * (c - 8) = a * c - 8 * a + 5 * b * c - 40 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 6 * b) * (c - 9) = a * c - 9 * a + 6 * b * c - 54 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 2 * b) * (c - 10) = a * c - 10 * a + 2 * b * c - 20 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 3 * b) * (c - 11) = a * c - 11 * a + 3 * b * c - 33 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 4 * b) * (c - 12) = a * c - 12 * a + 4 * b * c - 48 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 5 * b) * (c - 13) = a * c - 13 * a + 5 * b * c - 65 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 6 * b) * (c - 14) = a * c - 14 * a + 6 * b * c - 84 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 2 * b) * (c - 15) = a * c - 15 * a + 2 * b * c - 30 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 3 * b) * (c - 16) = a * c - 16 * a + 3 * b * c - 48 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 4 * b) * (c - 17) = a * c - 17 * a + 4 * b * c - 68 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 5 * b) * (c - 18) = a * c - 18 * a + 5 * b * c - 90 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 6 * b) * (c - 19) = a * c - 19 * a + 6 * b * c - 114 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 2 * b) * (c - 20) = a * c - 20 * a + 2 * b * c - 40 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 3 * b) * (c - 21) = a * c - 21 * a + 3 * b * c - 63 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 4 * b) * (c - 22) = a * c - 22 * a + 4 * b * c - 88 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 5 * b) * (c - 23) = a * c - 23 * a + 5 * b * c - 115 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 6 * b) * (c - 24) = a * c - 24 * a + 6 * b * c - 144 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 2 * b) * (c - 25) = a * c - 25 * a + 2 * b * c - 50 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 3 * b) * (c - 26) = a * c - 26 * a + 3 * b * c - 78 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 4 * b) * (c - 27) = a * c - 27 * a + 4 * b * c - 108 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 5 * b) * (c - 28) = a * c - 28 * a + 5 * b * c - 140 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 6 * b) * (c - 29) = a * c - 29 * a + 6 * b * c - 174 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 2 * b) * (c - 30) = a * c - 30 * a + 2 * b * c - 60 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 3 * b) * (c - 31) = a * c - 31 * a + 3 * b * c - 93 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 4 * b) * (c - 32) = a * c - 32 * a + 4 * b * c - 128 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 5 * b) * (c - 33) = a * c - 33 * a + 5 * b * c - 165 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 6 * b) * (c - 34) = a * c - 34 * a + 6 * b * c - 204 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 2 * b) * (c - 35) = a * c - 35 * a + 2 * b * c - 70 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 3 * b) * (c - 36) = a * c - 36 * a + 3 * b * c - 108 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 4 * b) * (c - 37) = a * c - 37 * a + 4 * b * c - 148 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 5 * b) * (c - 38) = a * c - 38 * a + 5 * b * c - 190 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 6 * b) * (c - 39) = a * c - 39 * a + 6 * b * c - 234 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 2 * b) * (c - 40) = a * c - 40 * a + 2 * b * c - 80 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 3 * b) * (c - 41) = a * c - 41 * a + 3 * b * c - 123 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 4 * b) * (c - 42) = a * c - 42 * a + 4 * b * c - 168 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 5 * b) * (c - 43) = a * c - 43 * a + 5 * b * c - 215 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 6 * b) * (c - 44) = a * c - 44 * a + 6 * b * c - 264 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 2 * b) * (c - 45) = a * c - 45 * a + 2 * b * c - 90 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 3 * b) * (c - 46) = a * c - 46 * a + 3 * b * c - 138 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 4 * b) * (c - 47) = a * c - 47 * a + 4 * b * c - 188 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 5 * b) * (c - 48) = a * c - 48 * a + 5 * b * c - 240 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 6 * b) * (c - 49) = a * c - 49 * a + 6 * b * c - 294 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 2 * b) * (c - 50) = a * c - 50 * a + 2 * b * c - 100 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 3 * b) * (c - 51) = a * c - 51 * a + 3 * b * c - 153 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 4 * b) * (c - 52) = a * c - 52 * a + 4 * b * c - 208 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 5 * b) * (c - 53) = a * c - 53 * a + 5 * b * c - 265 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 6 * b) * (c - 54) = a * c - 54 * a + 6 * b * c - 324 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 2 * b) * (c - 55) = a * c - 55 * a + 2 * b * c - 110 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 3 * b) * (c - 56) = a * c - 56 * a + 3 * b * c - 168 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 4 * b) * (c - 57) = a * c - 57 * a + 4 * b * c - 228 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 5 * b) * (c - 58) = a * c - 58 * a + 5 * b * c - 290 * b := by sym => simp arithSimp
example (a b c : Int) : (a + 6 * b) * (c - 59) = a * c - 59 * a + 6 * b * c - 354 * b := by sym => simp arithSimp
example (a b : Nat) : (a + 0 * b + 1)^2 = a^2 + 0 * a * b + 2 * a + 0 * b^2 + 0 * b + 1 := by sym => simp arithSimp
example (a b : Nat) : (a + 1 * b + 2)^2 = a^2 + 2 * a * b + 4 * a + 1 * b^2 + 4 * b + 4 := by sym => simp arithSimp
example (a b : Nat) : (a + 2 * b + 3)^2 = a^2 + 4 * a * b + 6 * a + 4 * b^2 + 12 * b + 9 := by sym => simp arithSimp
example (a b : Nat) : (a + 3 * b + 4)^2 = a^2 + 6 * a * b + 8 * a + 9 * b^2 + 24 * b + 16 := by sym => simp arithSimp
example (a b : Nat) : (a + 4 * b + 5)^2 = a^2 + 8 * a * b + 10 * a + 16 * b^2 + 40 * b + 25 := by sym => simp arithSimp
example (a b : Nat) : (a + 5 * b + 6)^2 = a^2 + 10 * a * b + 12 * a + 25 * b^2 + 60 * b + 36 := by sym => simp arithSimp
example (a b : Nat) : (a + 6 * b + 7)^2 = a^2 + 12 * a * b + 14 * a + 36 * b^2 + 84 * b + 49 := by sym => simp arithSimp
example (a b : Nat) : (a + 7 * b + 8)^2 = a^2 + 14 * a * b + 16 * a + 49 * b^2 + 112 * b + 64 := by sym => simp arithSimp
example (a b : Nat) : (a + 8 * b + 9)^2 = a^2 + 16 * a * b + 18 * a + 64 * b^2 + 144 * b + 81 := by sym => simp arithSimp
example (a b : Nat) : (a + 9 * b + 10)^2 = a^2 + 18 * a * b + 20 * a + 81 * b^2 + 180 * b + 100 := by sym => simp arithSimp
example (a b : Nat) : (a + 10 * b + 11)^2 = a^2 + 20 * a * b + 22 * a + 100 * b^2 + 220 * b + 121 := by sym => simp arithSimp
example (a b : Nat) : (a + 11 * b + 12)^2 = a^2 + 22 * a * b + 24 * a + 121 * b^2 + 264 * b + 144 := by sym => simp arithSimp
example (a b : Nat) : (a + 12 * b + 13)^2 = a^2 + 24 * a * b + 26 * a + 144 * b^2 + 312 * b + 169 := by sym => simp arithSimp
example (a b : Nat) : (a + 13 * b + 14)^2 = a^2 + 26 * a * b + 28 * a + 169 * b^2 + 364 * b + 196 := by sym => simp arithSimp
example (a b : Nat) : (a + 14 * b + 15)^2 = a^2 + 28 * a * b + 30 * a + 196 * b^2 + 420 * b + 225 := by sym => simp arithSimp
example (a b : Nat) : (a + 15 * b + 16)^2 = a^2 + 30 * a * b + 32 * a + 225 * b^2 + 480 * b + 256 := by sym => simp arithSimp
example (a b : Nat) : (a + 16 * b + 17)^2 = a^2 + 32 * a * b + 34 * a + 256 * b^2 + 544 * b + 289 := by sym => simp arithSimp
example (a b : Nat) : (a + 17 * b + 18)^2 = a^2 + 34 * a * b + 36 * a + 289 * b^2 + 612 * b + 324 := by sym => simp arithSimp
example (a b : Nat) : (a + 18 * b + 19)^2 = a^2 + 36 * a * b + 38 * a + 324 * b^2 + 684 * b + 361 := by sym => simp arithSimp
example (a b : Nat) : (a + 19 * b + 20)^2 = a^2 + 38 * a * b + 40 * a + 361 * b^2 + 760 * b + 400 := by sym => simp arithSimp
