/-!
Benchmark for the `arith` simproc of `Sym.simp` over fields: numeral denominators, inverses of
atoms, and expansions with rational coefficients.
-/

set_option sym.arith.maxTerms 1000
set_option sym.arith.maxDegree 1000

register_sym_simp arithSimp where
  pre  := arith >> control >> arrow_telescope
  post := ground

example (a b c d e f : Rat) : a / 2 + b / 3 + c / 5 + d / 7 + e / 11 + f / 13 = (15015 * a + 10010 * b + 6006 * c + 4290 * d + 2730 * e + 2310 * f) / 30030 := by sym => simp arithSimp

example (a b c : Rat) : (a + b) / c + (b + c) / a + (c + a) / b = a * c⁻¹ + b * c⁻¹ + b * a⁻¹ + c * a⁻¹ + c * b⁻¹ + a * b⁻¹ := by sym => simp arithSimp

example (x y z : Rat) : (x / 3 + y / 4 + z / 5)^8 = (20 * x + 15 * y + 12 * z)^8 / 167961600000000 := by sym => simp arithSimp

example [Lean.Grind.Field α] [Lean.Grind.IsCharP α 0] (x y : α) : (x / 2 + y / 3)^12 = (3 * x + 2 * y)^12 / 2176782336 := by sym => simp arithSimp

example [Lean.Grind.Field α] (x y z : α) : (x * y⁻¹ + z)^3 = x^3 * y⁻¹^3 + 3 * x^2 * y⁻¹^2 * z + 3 * x * y⁻¹ * z^2 + z^3 := by sym => simp arithSimp

example (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 x42 x43 x44 x45 x46 x47 x48 x49 x50 x51 x52 x53 x54 x55 x56 x57 x58 x59 x60 x61 x62 x63 x64 x65 x66 x67 x68 x69 x70 x71 x72 x73 x74 x75 x76 x77 x78 x79 x80 x81 x82 x83 x84 x85 x86 x87 x88 x89 x90 x91 x92 x93 x94 x95 x96 x97 x98 x99 : Rat) :
    x0 / 2 + x1 / 3 + x2 / 4 + x3 / 5 + x4 / 6 + x5 / 7 + x6 / 8 + x7 / 9 + x8 / 10 + x9 / 2 + x10 / 3 + x11 / 4 + x12 / 5 + x13 / 6 + x14 / 7 + x15 / 8 + x16 / 9 + x17 / 10 + x18 / 2 + x19 / 3 + x20 / 4 + x21 / 5 + x22 / 6 + x23 / 7 + x24 / 8 + x25 / 9 + x26 / 10 + x27 / 2 + x28 / 3 + x29 / 4 + x30 / 5 + x31 / 6 + x32 / 7 + x33 / 8 + x34 / 9 + x35 / 10 + x36 / 2 + x37 / 3 + x38 / 4 + x39 / 5 + x40 / 6 + x41 / 7 + x42 / 8 + x43 / 9 + x44 / 10 + x45 / 2 + x46 / 3 + x47 / 4 + x48 / 5 + x49 / 6 + x50 / 7 + x51 / 8 + x52 / 9 + x53 / 10 + x54 / 2 + x55 / 3 + x56 / 4 + x57 / 5 + x58 / 6 + x59 / 7 + x60 / 8 + x61 / 9 + x62 / 10 + x63 / 2 + x64 / 3 + x65 / 4 + x66 / 5 + x67 / 6 + x68 / 7 + x69 / 8 + x70 / 9 + x71 / 10 + x72 / 2 + x73 / 3 + x74 / 4 + x75 / 5 + x76 / 6 + x77 / 7 + x78 / 8 + x79 / 9 + x80 / 10 + x81 / 2 + x82 / 3 + x83 / 4 + x84 / 5 + x85 / 6 + x86 / 7 + x87 / 8 + x88 / 9 + x89 / 10 + x90 / 2 + x91 / 3 + x92 / 4 + x93 / 5 + x94 / 6 + x95 / 7 + x96 / 8 + x97 / 9 + x98 / 10 + x99 / 2 =
    x99 / 2 + x98 / 10 + x97 / 9 + x96 / 8 + x95 / 7 + x94 / 6 + x93 / 5 + x92 / 4 + x91 / 3 + x90 / 2 + x89 / 10 + x88 / 9 + x87 / 8 + x86 / 7 + x85 / 6 + x84 / 5 + x83 / 4 + x82 / 3 + x81 / 2 + x80 / 10 + x79 / 9 + x78 / 8 + x77 / 7 + x76 / 6 + x75 / 5 + x74 / 4 + x73 / 3 + x72 / 2 + x71 / 10 + x70 / 9 + x69 / 8 + x68 / 7 + x67 / 6 + x66 / 5 + x65 / 4 + x64 / 3 + x63 / 2 + x62 / 10 + x61 / 9 + x60 / 8 + x59 / 7 + x58 / 6 + x57 / 5 + x56 / 4 + x55 / 3 + x54 / 2 + x53 / 10 + x52 / 9 + x51 / 8 + x50 / 7 + x49 / 6 + x48 / 5 + x47 / 4 + x46 / 3 + x45 / 2 + x44 / 10 + x43 / 9 + x42 / 8 + x41 / 7 + x40 / 6 + x39 / 5 + x38 / 4 + x37 / 3 + x36 / 2 + x35 / 10 + x34 / 9 + x33 / 8 + x32 / 7 + x31 / 6 + x30 / 5 + x29 / 4 + x28 / 3 + x27 / 2 + x26 / 10 + x25 / 9 + x24 / 8 + x23 / 7 + x22 / 6 + x21 / 5 + x20 / 4 + x19 / 3 + x18 / 2 + x17 / 10 + x16 / 9 + x15 / 8 + x14 / 7 + x13 / 6 + x12 / 5 + x11 / 4 + x10 / 3 + x9 / 2 + x8 / 10 + x7 / 9 + x6 / 8 + x5 / 7 + x4 / 6 + x3 / 5 + x2 / 4 + x1 / 3 + x0 / 2 := by sym => simp arithSimp

example (x y z w : Rat) : (x / 2 + y / 3 + z / 5 + w / 7)^6 = (105 * x + 70 * y + 42 * z + 30 * w)^6 / 85766121000000 := by sym => simp arithSimp
