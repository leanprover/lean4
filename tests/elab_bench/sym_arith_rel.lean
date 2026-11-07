/-!
Benchmark for the `arith` simproc of `Sym.simp` on equalities and inequalities over `Int`, `Nat`,
`Rat` and ordered commutative rings.
-/

set_option sym.arith.maxTerms 1000
set_option sym.arith.maxDegree 1000

register_sym_simp arithSimp where
  pre  := arith >> control >> arrow_telescope
  post := ground

example (a b c d : Int) : ((a + b)^2 ≤ (c + d)^2) = (a^2 + 2*a*b + b^2 ≤ c^2 + 2*c*d + d^2) := by sym => simp arithSimp

example (a b c d : Int) : ((a + b + c + d)^6 < (a + b + c + d)^2 * (a + b + c + d)^4 + 1) = ((d + c + b + a)^6 < (a + b + c + d)^6 + 1) := by sym => simp arithSimp

example (a b c d : Nat) : ((a + b)^2 ≤ (c + d)^2) = (a^2 + 2*a*b + b^2 ≤ c^2 + 2*c*d + d^2) := by sym => simp arithSimp

example (a b c d : Nat) : ((a + b + c + d)^6 < (a + b + c + d)^2 * (a + b + c + d)^4 + 1) = ((d + c + b + a)^6 < (a + b + c + d)^6 + 1) := by sym => simp arithSimp

example (a b c d : Rat) : ((a + b)^2 ≤ (c + d)^2) = (a^2 + 2*a*b + b^2 ≤ c^2 + 2*c*d + d^2) := by sym => simp arithSimp

example (a b c d : Rat) : ((a + b + c + d)^6 < (a + b + c + d)^2 * (a + b + c + d)^4 + 1) = ((d + c + b + a)^6 < (a + b + c + d)^6 + 1) := by sym => simp arithSimp

example (a b c : Int) : (2 * (a + b + c) < 4 * (a - b) + 6 * c) = (6 * b < 2 * a + 4 * c) := by sym => simp arithSimp

example (x y : Rat) : (x / 2 + y / 3 = 1) = (3 * x + 2 * y = 6) := by sym => simp arithSimp

example (a b c d e : Int) : ((a + b + c + d + e)^2 = 0) = ((e + d + c + b + a)^2 = 0) := by sym => simp arithSimp

example (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 x42 x43 x44 x45 x46 x47 x48 x49 x50 x51 x52 x53 x54 x55 x56 x57 x58 x59 x60 x61 x62 x63 x64 x65 x66 x67 x68 x69 x70 x71 x72 x73 x74 x75 x76 x77 x78 x79 x80 x81 x82 x83 x84 x85 x86 x87 x88 x89 x90 x91 x92 x93 x94 x95 x96 x97 x98 x99 : Int) :
    (1 * x0 + 2 * x1 + 3 * x2 + 4 * x3 + 5 * x4 + 1 * x5 + 2 * x6 + 3 * x7 + 4 * x8 + 5 * x9 + 1 * x10 + 2 * x11 + 3 * x12 + 4 * x13 + 5 * x14 + 1 * x15 + 2 * x16 + 3 * x17 + 4 * x18 + 5 * x19 + 1 * x20 + 2 * x21 + 3 * x22 + 4 * x23 + 5 * x24 + 1 * x25 + 2 * x26 + 3 * x27 + 4 * x28 + 5 * x29 + 1 * x30 + 2 * x31 + 3 * x32 + 4 * x33 + 5 * x34 + 1 * x35 + 2 * x36 + 3 * x37 + 4 * x38 + 5 * x39 + 1 * x40 + 2 * x41 + 3 * x42 + 4 * x43 + 5 * x44 + 1 * x45 + 2 * x46 + 3 * x47 + 4 * x48 + 5 * x49 + 1 * x50 + 2 * x51 + 3 * x52 + 4 * x53 + 5 * x54 + 1 * x55 + 2 * x56 + 3 * x57 + 4 * x58 + 5 * x59 + 1 * x60 + 2 * x61 + 3 * x62 + 4 * x63 + 5 * x64 + 1 * x65 + 2 * x66 + 3 * x67 + 4 * x68 + 5 * x69 + 1 * x70 + 2 * x71 + 3 * x72 + 4 * x73 + 5 * x74 + 1 * x75 + 2 * x76 + 3 * x77 + 4 * x78 + 5 * x79 + 1 * x80 + 2 * x81 + 3 * x82 + 4 * x83 + 5 * x84 + 1 * x85 + 2 * x86 + 3 * x87 + 4 * x88 + 5 * x89 + 1 * x90 + 2 * x91 + 3 * x92 + 4 * x93 + 5 * x94 + 1 * x95 + 2 * x96 + 3 * x97 + 4 * x98 + 5 * x99 ≤ 0) = (5 * x99 + 4 * x98 + 3 * x97 + 2 * x96 + 1 * x95 + 5 * x94 + 4 * x93 + 3 * x92 + 2 * x91 + 1 * x90 + 5 * x89 + 4 * x88 + 3 * x87 + 2 * x86 + 1 * x85 + 5 * x84 + 4 * x83 + 3 * x82 + 2 * x81 + 1 * x80 + 5 * x79 + 4 * x78 + 3 * x77 + 2 * x76 + 1 * x75 + 5 * x74 + 4 * x73 + 3 * x72 + 2 * x71 + 1 * x70 + 5 * x69 + 4 * x68 + 3 * x67 + 2 * x66 + 1 * x65 + 5 * x64 + 4 * x63 + 3 * x62 + 2 * x61 + 1 * x60 + 5 * x59 + 4 * x58 + 3 * x57 + 2 * x56 + 1 * x55 + 5 * x54 + 4 * x53 + 3 * x52 + 2 * x51 + 1 * x50 + 5 * x49 + 4 * x48 + 3 * x47 + 2 * x46 + 1 * x45 + 5 * x44 + 4 * x43 + 3 * x42 + 2 * x41 + 1 * x40 + 5 * x39 + 4 * x38 + 3 * x37 + 2 * x36 + 1 * x35 + 5 * x34 + 4 * x33 + 3 * x32 + 2 * x31 + 1 * x30 + 5 * x29 + 4 * x28 + 3 * x27 + 2 * x26 + 1 * x25 + 5 * x24 + 4 * x23 + 3 * x22 + 2 * x21 + 1 * x20 + 5 * x19 + 4 * x18 + 3 * x17 + 2 * x16 + 1 * x15 + 5 * x14 + 4 * x13 + 3 * x12 + 2 * x11 + 1 * x10 + 5 * x9 + 4 * x8 + 3 * x7 + 2 * x6 + 1 * x5 + 5 * x4 + 4 * x3 + 3 * x2 + 2 * x1 + 1 * x0 ≤ 0) := by sym => simp arithSimp

example (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 x42 x43 x44 x45 x46 x47 x48 x49 x50 x51 x52 x53 x54 x55 x56 x57 x58 x59 x60 x61 x62 x63 x64 x65 x66 x67 x68 x69 x70 x71 x72 x73 x74 x75 x76 x77 x78 x79 x80 x81 x82 x83 x84 x85 x86 x87 x88 x89 x90 x91 x92 x93 x94 x95 x96 x97 x98 x99 : Nat) :
    (1 * x0 + 2 * x1 + 3 * x2 + 4 * x3 + 5 * x4 + 1 * x5 + 2 * x6 + 3 * x7 + 4 * x8 + 5 * x9 + 1 * x10 + 2 * x11 + 3 * x12 + 4 * x13 + 5 * x14 + 1 * x15 + 2 * x16 + 3 * x17 + 4 * x18 + 5 * x19 + 1 * x20 + 2 * x21 + 3 * x22 + 4 * x23 + 5 * x24 + 1 * x25 + 2 * x26 + 3 * x27 + 4 * x28 + 5 * x29 + 1 * x30 + 2 * x31 + 3 * x32 + 4 * x33 + 5 * x34 + 1 * x35 + 2 * x36 + 3 * x37 + 4 * x38 + 5 * x39 + 1 * x40 + 2 * x41 + 3 * x42 + 4 * x43 + 5 * x44 + 1 * x45 + 2 * x46 + 3 * x47 + 4 * x48 + 5 * x49 + 1 * x50 + 2 * x51 + 3 * x52 + 4 * x53 + 5 * x54 + 1 * x55 + 2 * x56 + 3 * x57 + 4 * x58 + 5 * x59 + 1 * x60 + 2 * x61 + 3 * x62 + 4 * x63 + 5 * x64 + 1 * x65 + 2 * x66 + 3 * x67 + 4 * x68 + 5 * x69 + 1 * x70 + 2 * x71 + 3 * x72 + 4 * x73 + 5 * x74 + 1 * x75 + 2 * x76 + 3 * x77 + 4 * x78 + 5 * x79 + 1 * x80 + 2 * x81 + 3 * x82 + 4 * x83 + 5 * x84 + 1 * x85 + 2 * x86 + 3 * x87 + 4 * x88 + 5 * x89 + 1 * x90 + 2 * x91 + 3 * x92 + 4 * x93 + 5 * x94 + 1 * x95 + 2 * x96 + 3 * x97 + 4 * x98 + 5 * x99 + 1 ≤ x0) = (5 * x99 + 4 * x98 + 3 * x97 + 2 * x96 + 1 * x95 + 5 * x94 + 4 * x93 + 3 * x92 + 2 * x91 + 1 * x90 + 5 * x89 + 4 * x88 + 3 * x87 + 2 * x86 + 1 * x85 + 5 * x84 + 4 * x83 + 3 * x82 + 2 * x81 + 1 * x80 + 5 * x79 + 4 * x78 + 3 * x77 + 2 * x76 + 1 * x75 + 5 * x74 + 4 * x73 + 3 * x72 + 2 * x71 + 1 * x70 + 5 * x69 + 4 * x68 + 3 * x67 + 2 * x66 + 1 * x65 + 5 * x64 + 4 * x63 + 3 * x62 + 2 * x61 + 1 * x60 + 5 * x59 + 4 * x58 + 3 * x57 + 2 * x56 + 1 * x55 + 5 * x54 + 4 * x53 + 3 * x52 + 2 * x51 + 1 * x50 + 5 * x49 + 4 * x48 + 3 * x47 + 2 * x46 + 1 * x45 + 5 * x44 + 4 * x43 + 3 * x42 + 2 * x41 + 1 * x40 + 5 * x39 + 4 * x38 + 3 * x37 + 2 * x36 + 1 * x35 + 5 * x34 + 4 * x33 + 3 * x32 + 2 * x31 + 1 * x30 + 5 * x29 + 4 * x28 + 3 * x27 + 2 * x26 + 1 * x25 + 5 * x24 + 4 * x23 + 3 * x22 + 2 * x21 + 1 * x20 + 5 * x19 + 4 * x18 + 3 * x17 + 2 * x16 + 1 * x15 + 5 * x14 + 4 * x13 + 3 * x12 + 2 * x11 + 1 * x10 + 5 * x9 + 4 * x8 + 3 * x7 + 2 * x6 + 1 * x5 + 5 * x4 + 4 * x3 + 3 * x2 + 2 * x1 + 1 * x0 + 1 ≤ x0) := by sym => simp arithSimp

example [Lean.Grind.CommRing α] [LE α] [LT α] [Std.IsPreorder α] [Lean.Grind.OrderedRing α] (a b c : α) : ((a + b + c)^2 ≤ a * b) = ((c + b + a)^2 ≤ b * a) := by sym => simp arithSimp
