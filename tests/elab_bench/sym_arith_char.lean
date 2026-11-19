/-!
Benchmark for the `arith` simproc of `Sym.simp` in rings with a nonzero characteristic:
fixed-width integers, bit vectors and `Fin`.
-/

set_option sym.arith.maxTerms 1000
set_option sym.arith.maxDegree 1000

register_sym_simp arithSimp where
  pre  := arith >> control >> arrow_telescope
  post := ground

example (x y : UInt8) : (x + y)^24 = (x + y)^12 * (x + y)^12 := by sym => simp arithSimp

example (x y z : UInt64) : (x + 3 * y + 5 * z)^10 = (x + 3 * y + 5 * z)^4 * (x + 3 * y + 5 * z)^6 := by sym => simp arithSimp

example (x y z : BitVec 16) : (x + 3 * y + 5 * z)^8 = ((x + 3 * y + 5 * z)^2)^4 := by sym => simp arithSimp

example (x y z : BitVec 64) : (x - y) * (x + y) * (x * x + y * y) + 255 * z = x^4 - y^4 - z + 256 * z := by sym => simp arithSimp

example (x y z w : BitVec 64) : (x + y + z + w)^7 = (w + z + y + x)^3 * (x + y + z + w)^4 := by sym => simp arithSimp

example (x y : Fin 13) : (x + y)^26 = (x + y)^13 * (x + y)^13 := by sym => simp arithSimp

example (x y : Int8) : (x + 200 * y)^18 = ((x + 200 * y)^6)^3 := by sym => simp arithSimp

example (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 x42 x43 x44 x45 x46 x47 x48 x49 x50 x51 x52 x53 x54 x55 x56 x57 x58 x59 x60 x61 x62 x63 x64 x65 x66 x67 x68 x69 x70 x71 x72 x73 x74 x75 x76 x77 x78 x79 x80 x81 x82 x83 x84 x85 x86 x87 x88 x89 x90 x91 x92 x93 x94 x95 x96 x97 x98 x99 : UInt8) :
    1 * x0 + 38 * x1 + 75 * x2 + 112 * x3 + 149 * x4 + 186 * x5 + 223 * x6 + 9 * x7 + 46 * x8 + 83 * x9 + 120 * x10 + 157 * x11 + 194 * x12 + 231 * x13 + 17 * x14 + 54 * x15 + 91 * x16 + 128 * x17 + 165 * x18 + 202 * x19 + 239 * x20 + 25 * x21 + 62 * x22 + 99 * x23 + 136 * x24 + 173 * x25 + 210 * x26 + 247 * x27 + 33 * x28 + 70 * x29 + 107 * x30 + 144 * x31 + 181 * x32 + 218 * x33 + 4 * x34 + 41 * x35 + 78 * x36 + 115 * x37 + 152 * x38 + 189 * x39 + 226 * x40 + 12 * x41 + 49 * x42 + 86 * x43 + 123 * x44 + 160 * x45 + 197 * x46 + 234 * x47 + 20 * x48 + 57 * x49 + 94 * x50 + 131 * x51 + 168 * x52 + 205 * x53 + 242 * x54 + 28 * x55 + 65 * x56 + 102 * x57 + 139 * x58 + 176 * x59 + 213 * x60 + 250 * x61 + 36 * x62 + 73 * x63 + 110 * x64 + 147 * x65 + 184 * x66 + 221 * x67 + 7 * x68 + 44 * x69 + 81 * x70 + 118 * x71 + 155 * x72 + 192 * x73 + 229 * x74 + 15 * x75 + 52 * x76 + 89 * x77 + 126 * x78 + 163 * x79 + 200 * x80 + 237 * x81 + 23 * x82 + 60 * x83 + 97 * x84 + 134 * x85 + 171 * x86 + 208 * x87 + 245 * x88 + 31 * x89 + 68 * x90 + 105 * x91 + 142 * x92 + 179 * x93 + 216 * x94 + 2 * x95 + 39 * x96 + 76 * x97 + 113 * x98 + 150 * x99 =
    150 * x99 + 113 * x98 + 76 * x97 + 39 * x96 + 2 * x95 + 216 * x94 + 179 * x93 + 142 * x92 + 105 * x91 + 68 * x90 + 31 * x89 + 245 * x88 + 208 * x87 + 171 * x86 + 134 * x85 + 97 * x84 + 60 * x83 + 23 * x82 + 237 * x81 + 200 * x80 + 163 * x79 + 126 * x78 + 89 * x77 + 52 * x76 + 15 * x75 + 229 * x74 + 192 * x73 + 155 * x72 + 118 * x71 + 81 * x70 + 44 * x69 + 7 * x68 + 221 * x67 + 184 * x66 + 147 * x65 + 110 * x64 + 73 * x63 + 36 * x62 + 250 * x61 + 213 * x60 + 176 * x59 + 139 * x58 + 102 * x57 + 65 * x56 + 28 * x55 + 242 * x54 + 205 * x53 + 168 * x52 + 131 * x51 + 94 * x50 + 57 * x49 + 20 * x48 + 234 * x47 + 197 * x46 + 160 * x45 + 123 * x44 + 86 * x43 + 49 * x42 + 12 * x41 + 226 * x40 + 189 * x39 + 152 * x38 + 115 * x37 + 78 * x36 + 41 * x35 + 4 * x34 + 218 * x33 + 181 * x32 + 144 * x31 + 107 * x30 + 70 * x29 + 33 * x28 + 247 * x27 + 210 * x26 + 173 * x25 + 136 * x24 + 99 * x23 + 62 * x22 + 25 * x21 + 239 * x20 + 202 * x19 + 165 * x18 + 128 * x17 + 91 * x16 + 54 * x15 + 17 * x14 + 231 * x13 + 194 * x12 + 157 * x11 + 120 * x10 + 83 * x9 + 46 * x8 + 9 * x7 + 223 * x6 + 186 * x5 + 149 * x4 + 112 * x3 + 75 * x2 + 38 * x1 + 1 * x0 := by sym => simp arithSimp
