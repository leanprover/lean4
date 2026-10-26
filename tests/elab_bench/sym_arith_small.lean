/-!
Benchmark for the `arith` simproc of `Sym.simp` on many small goals over `Int`, `Nat` and `Rat`,
measuring the per-goal overhead.
-/

set_option sym.arith.maxTerms 1000
set_option sym.arith.maxDegree 1000

register_sym_simp arithSimp where
  pre  := arith >> control >> arrow_telescope
  post := ground

example (a b c : Nat) : (a + 3 * b) * (c + 1) = a * c + 1 * a + 3 * b * c + 3 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 4) * (c - 2) = a * c - 2 * a + b * c / 4 - 2 * b / 4 := by sym => simp arithSimp
example (a b c : Int) : (a + 5 * b) * (c - 3) = a * c - 3 * a + 5 * b * c - 15 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 6 * b) * (c + 4) = a * c + 4 * a + 6 * b * c + 24 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 2) * (c - 5) = a * c - 5 * a + b * c / 2 - 5 * b / 2 := by sym => simp arithSimp
example (a b c : Int) : (a + 3 * b) * (c - 6) = a * c - 6 * a + 3 * b * c - 18 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 4 * b) * (c + 7) = a * c + 7 * a + 4 * b * c + 28 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 5) * (c - 8) = a * c - 8 * a + b * c / 5 - 8 * b / 5 := by sym => simp arithSimp
example (a b c : Int) : (a + 6 * b) * (c - 9) = a * c - 9 * a + 6 * b * c - 54 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 2 * b) * (c + 10) = a * c + 10 * a + 2 * b * c + 20 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 3) * (c - 11) = a * c - 11 * a + b * c / 3 - 11 * b / 3 := by sym => simp arithSimp
example (a b c : Int) : (a + 4 * b) * (c - 12) = a * c - 12 * a + 4 * b * c - 48 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 5 * b) * (c + 13) = a * c + 13 * a + 5 * b * c + 65 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 6) * (c - 14) = a * c - 14 * a + b * c / 6 - 14 * b / 6 := by sym => simp arithSimp
example (a b c : Int) : (a + 2 * b) * (c - 15) = a * c - 15 * a + 2 * b * c - 30 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 3 * b) * (c + 16) = a * c + 16 * a + 3 * b * c + 48 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 4) * (c - 17) = a * c - 17 * a + b * c / 4 - 17 * b / 4 := by sym => simp arithSimp
example (a b c : Int) : (a + 5 * b) * (c - 18) = a * c - 18 * a + 5 * b * c - 90 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 6 * b) * (c + 19) = a * c + 19 * a + 6 * b * c + 114 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 2) * (c - 20) = a * c - 20 * a + b * c / 2 - 20 * b / 2 := by sym => simp arithSimp
example (a b c : Int) : (a + 3 * b) * (c - 21) = a * c - 21 * a + 3 * b * c - 63 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 4 * b) * (c + 22) = a * c + 22 * a + 4 * b * c + 88 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 5) * (c - 23) = a * c - 23 * a + b * c / 5 - 23 * b / 5 := by sym => simp arithSimp
example (a b c : Int) : (a + 6 * b) * (c - 24) = a * c - 24 * a + 6 * b * c - 144 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 2 * b) * (c + 25) = a * c + 25 * a + 2 * b * c + 50 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 3) * (c - 26) = a * c - 26 * a + b * c / 3 - 26 * b / 3 := by sym => simp arithSimp
example (a b c : Int) : (a + 4 * b) * (c - 27) = a * c - 27 * a + 4 * b * c - 108 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 5 * b) * (c + 28) = a * c + 28 * a + 5 * b * c + 140 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 6) * (c - 29) = a * c - 29 * a + b * c / 6 - 29 * b / 6 := by sym => simp arithSimp
example (a b c : Int) : (a + 2 * b) * (c - 30) = a * c - 30 * a + 2 * b * c - 60 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 3 * b) * (c + 31) = a * c + 31 * a + 3 * b * c + 93 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 4) * (c - 32) = a * c - 32 * a + b * c / 4 - 32 * b / 4 := by sym => simp arithSimp
example (a b c : Int) : (a + 5 * b) * (c - 33) = a * c - 33 * a + 5 * b * c - 165 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 6 * b) * (c + 34) = a * c + 34 * a + 6 * b * c + 204 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 2) * (c - 35) = a * c - 35 * a + b * c / 2 - 35 * b / 2 := by sym => simp arithSimp
example (a b c : Int) : (a + 3 * b) * (c - 36) = a * c - 36 * a + 3 * b * c - 108 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 4 * b) * (c + 37) = a * c + 37 * a + 4 * b * c + 148 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 5) * (c - 38) = a * c - 38 * a + b * c / 5 - 38 * b / 5 := by sym => simp arithSimp
example (a b c : Int) : (a + 6 * b) * (c - 39) = a * c - 39 * a + 6 * b * c - 234 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 2 * b) * (c + 40) = a * c + 40 * a + 2 * b * c + 80 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 3) * (c - 41) = a * c - 41 * a + b * c / 3 - 41 * b / 3 := by sym => simp arithSimp
example (a b c : Int) : (a + 4 * b) * (c - 42) = a * c - 42 * a + 4 * b * c - 168 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 5 * b) * (c + 43) = a * c + 43 * a + 5 * b * c + 215 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 6) * (c - 44) = a * c - 44 * a + b * c / 6 - 44 * b / 6 := by sym => simp arithSimp
example (a b c : Int) : (a + 2 * b) * (c - 45) = a * c - 45 * a + 2 * b * c - 90 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 3 * b) * (c + 46) = a * c + 46 * a + 3 * b * c + 138 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 4) * (c - 47) = a * c - 47 * a + b * c / 4 - 47 * b / 4 := by sym => simp arithSimp
example (a b c : Int) : (a + 5 * b) * (c - 48) = a * c - 48 * a + 5 * b * c - 240 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 6 * b) * (c + 49) = a * c + 49 * a + 6 * b * c + 294 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 2) * (c - 50) = a * c - 50 * a + b * c / 2 - 50 * b / 2 := by sym => simp arithSimp
example (a b c : Int) : (a + 3 * b) * (c - 51) = a * c - 51 * a + 3 * b * c - 153 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 4 * b) * (c + 52) = a * c + 52 * a + 4 * b * c + 208 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 5) * (c - 53) = a * c - 53 * a + b * c / 5 - 53 * b / 5 := by sym => simp arithSimp
example (a b c : Int) : (a + 6 * b) * (c - 54) = a * c - 54 * a + 6 * b * c - 324 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 2 * b) * (c + 55) = a * c + 55 * a + 2 * b * c + 110 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 3) * (c - 56) = a * c - 56 * a + b * c / 3 - 56 * b / 3 := by sym => simp arithSimp
example (a b c : Int) : (a + 4 * b) * (c - 57) = a * c - 57 * a + 4 * b * c - 228 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 5 * b) * (c + 58) = a * c + 58 * a + 5 * b * c + 290 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 6) * (c - 59) = a * c - 59 * a + b * c / 6 - 59 * b / 6 := by sym => simp arithSimp
example (a b c : Int) : (a + 2 * b) * (c - 60) = a * c - 60 * a + 2 * b * c - 120 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 3 * b) * (c + 61) = a * c + 61 * a + 3 * b * c + 183 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 4) * (c - 62) = a * c - 62 * a + b * c / 4 - 62 * b / 4 := by sym => simp arithSimp
example (a b c : Int) : (a + 5 * b) * (c - 63) = a * c - 63 * a + 5 * b * c - 315 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 6 * b) * (c + 64) = a * c + 64 * a + 6 * b * c + 384 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 2) * (c - 65) = a * c - 65 * a + b * c / 2 - 65 * b / 2 := by sym => simp arithSimp
example (a b c : Int) : (a + 3 * b) * (c - 66) = a * c - 66 * a + 3 * b * c - 198 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 4 * b) * (c + 67) = a * c + 67 * a + 4 * b * c + 268 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 5) * (c - 68) = a * c - 68 * a + b * c / 5 - 68 * b / 5 := by sym => simp arithSimp
example (a b c : Int) : (a + 6 * b) * (c - 69) = a * c - 69 * a + 6 * b * c - 414 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 2 * b) * (c + 70) = a * c + 70 * a + 2 * b * c + 140 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 3) * (c - 71) = a * c - 71 * a + b * c / 3 - 71 * b / 3 := by sym => simp arithSimp
example (a b c : Int) : (a + 4 * b) * (c - 72) = a * c - 72 * a + 4 * b * c - 288 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 5 * b) * (c + 73) = a * c + 73 * a + 5 * b * c + 365 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 6) * (c - 74) = a * c - 74 * a + b * c / 6 - 74 * b / 6 := by sym => simp arithSimp
example (a b c : Int) : (a + 2 * b) * (c - 75) = a * c - 75 * a + 2 * b * c - 150 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 3 * b) * (c + 76) = a * c + 76 * a + 3 * b * c + 228 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 4) * (c - 77) = a * c - 77 * a + b * c / 4 - 77 * b / 4 := by sym => simp arithSimp
example (a b c : Int) : (a + 5 * b) * (c - 78) = a * c - 78 * a + 5 * b * c - 390 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 6 * b) * (c + 79) = a * c + 79 * a + 6 * b * c + 474 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 2) * (c - 80) = a * c - 80 * a + b * c / 2 - 80 * b / 2 := by sym => simp arithSimp
example (a b c : Int) : (a + 3 * b) * (c - 81) = a * c - 81 * a + 3 * b * c - 243 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 4 * b) * (c + 82) = a * c + 82 * a + 4 * b * c + 328 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 5) * (c - 83) = a * c - 83 * a + b * c / 5 - 83 * b / 5 := by sym => simp arithSimp
example (a b c : Int) : (a + 6 * b) * (c - 84) = a * c - 84 * a + 6 * b * c - 504 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 2 * b) * (c + 85) = a * c + 85 * a + 2 * b * c + 170 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 3) * (c - 86) = a * c - 86 * a + b * c / 3 - 86 * b / 3 := by sym => simp arithSimp
example (a b c : Int) : (a + 4 * b) * (c - 87) = a * c - 87 * a + 4 * b * c - 348 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 5 * b) * (c + 88) = a * c + 88 * a + 5 * b * c + 440 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 6) * (c - 89) = a * c - 89 * a + b * c / 6 - 89 * b / 6 := by sym => simp arithSimp
example (a b c : Int) : (a + 2 * b) * (c - 90) = a * c - 90 * a + 2 * b * c - 180 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 3 * b) * (c + 91) = a * c + 91 * a + 3 * b * c + 273 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 4) * (c - 92) = a * c - 92 * a + b * c / 4 - 92 * b / 4 := by sym => simp arithSimp
example (a b c : Int) : (a + 5 * b) * (c - 93) = a * c - 93 * a + 5 * b * c - 465 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 6 * b) * (c + 94) = a * c + 94 * a + 6 * b * c + 564 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 2) * (c - 95) = a * c - 95 * a + b * c / 2 - 95 * b / 2 := by sym => simp arithSimp
example (a b c : Int) : (a + 3 * b) * (c - 96) = a * c - 96 * a + 3 * b * c - 288 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 4 * b) * (c + 97) = a * c + 97 * a + 4 * b * c + 388 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 5) * (c - 98) = a * c - 98 * a + b * c / 5 - 98 * b / 5 := by sym => simp arithSimp
example (a b c : Int) : (a + 6 * b) * (c - 99) = a * c - 99 * a + 6 * b * c - 594 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 2 * b) * (c + 100) = a * c + 100 * a + 2 * b * c + 200 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 3) * (c - 101) = a * c - 101 * a + b * c / 3 - 101 * b / 3 := by sym => simp arithSimp
example (a b c : Int) : (a + 4 * b) * (c - 102) = a * c - 102 * a + 4 * b * c - 408 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 5 * b) * (c + 103) = a * c + 103 * a + 5 * b * c + 515 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 6) * (c - 104) = a * c - 104 * a + b * c / 6 - 104 * b / 6 := by sym => simp arithSimp
example (a b c : Int) : (a + 2 * b) * (c - 105) = a * c - 105 * a + 2 * b * c - 210 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 3 * b) * (c + 106) = a * c + 106 * a + 3 * b * c + 318 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 4) * (c - 107) = a * c - 107 * a + b * c / 4 - 107 * b / 4 := by sym => simp arithSimp
example (a b c : Int) : (a + 5 * b) * (c - 108) = a * c - 108 * a + 5 * b * c - 540 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 6 * b) * (c + 109) = a * c + 109 * a + 6 * b * c + 654 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 2) * (c - 110) = a * c - 110 * a + b * c / 2 - 110 * b / 2 := by sym => simp arithSimp
example (a b c : Int) : (a + 3 * b) * (c - 111) = a * c - 111 * a + 3 * b * c - 333 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 4 * b) * (c + 112) = a * c + 112 * a + 4 * b * c + 448 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 5) * (c - 113) = a * c - 113 * a + b * c / 5 - 113 * b / 5 := by sym => simp arithSimp
example (a b c : Int) : (a + 6 * b) * (c - 114) = a * c - 114 * a + 6 * b * c - 684 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 2 * b) * (c + 115) = a * c + 115 * a + 2 * b * c + 230 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 3) * (c - 116) = a * c - 116 * a + b * c / 3 - 116 * b / 3 := by sym => simp arithSimp
example (a b c : Int) : (a + 4 * b) * (c - 117) = a * c - 117 * a + 4 * b * c - 468 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 5 * b) * (c + 118) = a * c + 118 * a + 5 * b * c + 590 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 6) * (c - 119) = a * c - 119 * a + b * c / 6 - 119 * b / 6 := by sym => simp arithSimp
example (a b c : Int) : (a + 2 * b) * (c - 120) = a * c - 120 * a + 2 * b * c - 240 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 3 * b) * (c + 121) = a * c + 121 * a + 3 * b * c + 363 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 4) * (c - 122) = a * c - 122 * a + b * c / 4 - 122 * b / 4 := by sym => simp arithSimp
example (a b c : Int) : (a + 5 * b) * (c - 123) = a * c - 123 * a + 5 * b * c - 615 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 6 * b) * (c + 124) = a * c + 124 * a + 6 * b * c + 744 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 2) * (c - 125) = a * c - 125 * a + b * c / 2 - 125 * b / 2 := by sym => simp arithSimp
example (a b c : Int) : (a + 3 * b) * (c - 126) = a * c - 126 * a + 3 * b * c - 378 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 4 * b) * (c + 127) = a * c + 127 * a + 4 * b * c + 508 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 5) * (c - 128) = a * c - 128 * a + b * c / 5 - 128 * b / 5 := by sym => simp arithSimp
example (a b c : Int) : (a + 6 * b) * (c - 129) = a * c - 129 * a + 6 * b * c - 774 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 2 * b) * (c + 130) = a * c + 130 * a + 2 * b * c + 260 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 3) * (c - 131) = a * c - 131 * a + b * c / 3 - 131 * b / 3 := by sym => simp arithSimp
example (a b c : Int) : (a + 4 * b) * (c - 132) = a * c - 132 * a + 4 * b * c - 528 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 5 * b) * (c + 133) = a * c + 133 * a + 5 * b * c + 665 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 6) * (c - 134) = a * c - 134 * a + b * c / 6 - 134 * b / 6 := by sym => simp arithSimp
example (a b c : Int) : (a + 2 * b) * (c - 135) = a * c - 135 * a + 2 * b * c - 270 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 3 * b) * (c + 136) = a * c + 136 * a + 3 * b * c + 408 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 4) * (c - 137) = a * c - 137 * a + b * c / 4 - 137 * b / 4 := by sym => simp arithSimp
example (a b c : Int) : (a + 5 * b) * (c - 138) = a * c - 138 * a + 5 * b * c - 690 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 6 * b) * (c + 139) = a * c + 139 * a + 6 * b * c + 834 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 2) * (c - 140) = a * c - 140 * a + b * c / 2 - 140 * b / 2 := by sym => simp arithSimp
example (a b c : Int) : (a + 3 * b) * (c - 141) = a * c - 141 * a + 3 * b * c - 423 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 4 * b) * (c + 142) = a * c + 142 * a + 4 * b * c + 568 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 5) * (c - 143) = a * c - 143 * a + b * c / 5 - 143 * b / 5 := by sym => simp arithSimp
example (a b c : Int) : (a + 6 * b) * (c - 144) = a * c - 144 * a + 6 * b * c - 864 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 2 * b) * (c + 145) = a * c + 145 * a + 2 * b * c + 290 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 3) * (c - 146) = a * c - 146 * a + b * c / 3 - 146 * b / 3 := by sym => simp arithSimp
example (a b c : Int) : (a + 4 * b) * (c - 147) = a * c - 147 * a + 4 * b * c - 588 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 5 * b) * (c + 148) = a * c + 148 * a + 5 * b * c + 740 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 6) * (c - 149) = a * c - 149 * a + b * c / 6 - 149 * b / 6 := by sym => simp arithSimp
example (a b c : Int) : (a + 2 * b) * (c - 150) = a * c - 150 * a + 2 * b * c - 300 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 3 * b) * (c + 151) = a * c + 151 * a + 3 * b * c + 453 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 4) * (c - 152) = a * c - 152 * a + b * c / 4 - 152 * b / 4 := by sym => simp arithSimp
example (a b c : Int) : (a + 5 * b) * (c - 153) = a * c - 153 * a + 5 * b * c - 765 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 6 * b) * (c + 154) = a * c + 154 * a + 6 * b * c + 924 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 2) * (c - 155) = a * c - 155 * a + b * c / 2 - 155 * b / 2 := by sym => simp arithSimp
example (a b c : Int) : (a + 3 * b) * (c - 156) = a * c - 156 * a + 3 * b * c - 468 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 4 * b) * (c + 157) = a * c + 157 * a + 4 * b * c + 628 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 5) * (c - 158) = a * c - 158 * a + b * c / 5 - 158 * b / 5 := by sym => simp arithSimp
example (a b c : Int) : (a + 6 * b) * (c - 159) = a * c - 159 * a + 6 * b * c - 954 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 2 * b) * (c + 160) = a * c + 160 * a + 2 * b * c + 320 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 3) * (c - 161) = a * c - 161 * a + b * c / 3 - 161 * b / 3 := by sym => simp arithSimp
example (a b c : Int) : (a + 4 * b) * (c - 162) = a * c - 162 * a + 4 * b * c - 648 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 5 * b) * (c + 163) = a * c + 163 * a + 5 * b * c + 815 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 6) * (c - 164) = a * c - 164 * a + b * c / 6 - 164 * b / 6 := by sym => simp arithSimp
example (a b c : Int) : (a + 2 * b) * (c - 165) = a * c - 165 * a + 2 * b * c - 330 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 3 * b) * (c + 166) = a * c + 166 * a + 3 * b * c + 498 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 4) * (c - 167) = a * c - 167 * a + b * c / 4 - 167 * b / 4 := by sym => simp arithSimp
example (a b c : Int) : (a + 5 * b) * (c - 168) = a * c - 168 * a + 5 * b * c - 840 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 6 * b) * (c + 169) = a * c + 169 * a + 6 * b * c + 1014 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 2) * (c - 170) = a * c - 170 * a + b * c / 2 - 170 * b / 2 := by sym => simp arithSimp
example (a b c : Int) : (a + 3 * b) * (c - 171) = a * c - 171 * a + 3 * b * c - 513 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 4 * b) * (c + 172) = a * c + 172 * a + 4 * b * c + 688 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 5) * (c - 173) = a * c - 173 * a + b * c / 5 - 173 * b / 5 := by sym => simp arithSimp
example (a b c : Int) : (a + 6 * b) * (c - 174) = a * c - 174 * a + 6 * b * c - 1044 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 2 * b) * (c + 175) = a * c + 175 * a + 2 * b * c + 350 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 3) * (c - 176) = a * c - 176 * a + b * c / 3 - 176 * b / 3 := by sym => simp arithSimp
example (a b c : Int) : (a + 4 * b) * (c - 177) = a * c - 177 * a + 4 * b * c - 708 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 5 * b) * (c + 178) = a * c + 178 * a + 5 * b * c + 890 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 6) * (c - 179) = a * c - 179 * a + b * c / 6 - 179 * b / 6 := by sym => simp arithSimp
example (a b c : Int) : (a + 2 * b) * (c - 180) = a * c - 180 * a + 2 * b * c - 360 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 3 * b) * (c + 181) = a * c + 181 * a + 3 * b * c + 543 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 4) * (c - 182) = a * c - 182 * a + b * c / 4 - 182 * b / 4 := by sym => simp arithSimp
example (a b c : Int) : (a + 5 * b) * (c - 183) = a * c - 183 * a + 5 * b * c - 915 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 6 * b) * (c + 184) = a * c + 184 * a + 6 * b * c + 1104 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 2) * (c - 185) = a * c - 185 * a + b * c / 2 - 185 * b / 2 := by sym => simp arithSimp
example (a b c : Int) : (a + 3 * b) * (c - 186) = a * c - 186 * a + 3 * b * c - 558 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 4 * b) * (c + 187) = a * c + 187 * a + 4 * b * c + 748 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 5) * (c - 188) = a * c - 188 * a + b * c / 5 - 188 * b / 5 := by sym => simp arithSimp
example (a b c : Int) : (a + 6 * b) * (c - 189) = a * c - 189 * a + 6 * b * c - 1134 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 2 * b) * (c + 190) = a * c + 190 * a + 2 * b * c + 380 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 3) * (c - 191) = a * c - 191 * a + b * c / 3 - 191 * b / 3 := by sym => simp arithSimp
example (a b c : Int) : (a + 4 * b) * (c - 192) = a * c - 192 * a + 4 * b * c - 768 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 5 * b) * (c + 193) = a * c + 193 * a + 5 * b * c + 965 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 6) * (c - 194) = a * c - 194 * a + b * c / 6 - 194 * b / 6 := by sym => simp arithSimp
example (a b c : Int) : (a + 2 * b) * (c - 195) = a * c - 195 * a + 2 * b * c - 390 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 3 * b) * (c + 196) = a * c + 196 * a + 3 * b * c + 588 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 4) * (c - 197) = a * c - 197 * a + b * c / 4 - 197 * b / 4 := by sym => simp arithSimp
example (a b c : Int) : (a + 5 * b) * (c - 198) = a * c - 198 * a + 5 * b * c - 990 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 6 * b) * (c + 199) = a * c + 199 * a + 6 * b * c + 1194 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 2) * (c - 200) = a * c - 200 * a + b * c / 2 - 200 * b / 2 := by sym => simp arithSimp
example (a b c : Int) : (a + 3 * b) * (c - 201) = a * c - 201 * a + 3 * b * c - 603 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 4 * b) * (c + 202) = a * c + 202 * a + 4 * b * c + 808 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 5) * (c - 203) = a * c - 203 * a + b * c / 5 - 203 * b / 5 := by sym => simp arithSimp
example (a b c : Int) : (a + 6 * b) * (c - 204) = a * c - 204 * a + 6 * b * c - 1224 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 2 * b) * (c + 205) = a * c + 205 * a + 2 * b * c + 410 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 3) * (c - 206) = a * c - 206 * a + b * c / 3 - 206 * b / 3 := by sym => simp arithSimp
example (a b c : Int) : (a + 4 * b) * (c - 207) = a * c - 207 * a + 4 * b * c - 828 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 5 * b) * (c + 208) = a * c + 208 * a + 5 * b * c + 1040 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 6) * (c - 209) = a * c - 209 * a + b * c / 6 - 209 * b / 6 := by sym => simp arithSimp
example (a b c : Int) : (a + 2 * b) * (c - 210) = a * c - 210 * a + 2 * b * c - 420 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 3 * b) * (c + 211) = a * c + 211 * a + 3 * b * c + 633 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 4) * (c - 212) = a * c - 212 * a + b * c / 4 - 212 * b / 4 := by sym => simp arithSimp
example (a b c : Int) : (a + 5 * b) * (c - 213) = a * c - 213 * a + 5 * b * c - 1065 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 6 * b) * (c + 214) = a * c + 214 * a + 6 * b * c + 1284 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 2) * (c - 215) = a * c - 215 * a + b * c / 2 - 215 * b / 2 := by sym => simp arithSimp
example (a b c : Int) : (a + 3 * b) * (c - 216) = a * c - 216 * a + 3 * b * c - 648 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 4 * b) * (c + 217) = a * c + 217 * a + 4 * b * c + 868 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 5) * (c - 218) = a * c - 218 * a + b * c / 5 - 218 * b / 5 := by sym => simp arithSimp
example (a b c : Int) : (a + 6 * b) * (c - 219) = a * c - 219 * a + 6 * b * c - 1314 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 2 * b) * (c + 220) = a * c + 220 * a + 2 * b * c + 440 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 3) * (c - 221) = a * c - 221 * a + b * c / 3 - 221 * b / 3 := by sym => simp arithSimp
example (a b c : Int) : (a + 4 * b) * (c - 222) = a * c - 222 * a + 4 * b * c - 888 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 5 * b) * (c + 223) = a * c + 223 * a + 5 * b * c + 1115 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 6) * (c - 224) = a * c - 224 * a + b * c / 6 - 224 * b / 6 := by sym => simp arithSimp
example (a b c : Int) : (a + 2 * b) * (c - 225) = a * c - 225 * a + 2 * b * c - 450 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 3 * b) * (c + 226) = a * c + 226 * a + 3 * b * c + 678 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 4) * (c - 227) = a * c - 227 * a + b * c / 4 - 227 * b / 4 := by sym => simp arithSimp
example (a b c : Int) : (a + 5 * b) * (c - 228) = a * c - 228 * a + 5 * b * c - 1140 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 6 * b) * (c + 229) = a * c + 229 * a + 6 * b * c + 1374 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 2) * (c - 230) = a * c - 230 * a + b * c / 2 - 230 * b / 2 := by sym => simp arithSimp
example (a b c : Int) : (a + 3 * b) * (c - 231) = a * c - 231 * a + 3 * b * c - 693 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 4 * b) * (c + 232) = a * c + 232 * a + 4 * b * c + 928 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 5) * (c - 233) = a * c - 233 * a + b * c / 5 - 233 * b / 5 := by sym => simp arithSimp
example (a b c : Int) : (a + 6 * b) * (c - 234) = a * c - 234 * a + 6 * b * c - 1404 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 2 * b) * (c + 235) = a * c + 235 * a + 2 * b * c + 470 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 3) * (c - 236) = a * c - 236 * a + b * c / 3 - 236 * b / 3 := by sym => simp arithSimp
example (a b c : Int) : (a + 4 * b) * (c - 237) = a * c - 237 * a + 4 * b * c - 948 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 5 * b) * (c + 238) = a * c + 238 * a + 5 * b * c + 1190 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 6) * (c - 239) = a * c - 239 * a + b * c / 6 - 239 * b / 6 := by sym => simp arithSimp
example (a b c : Int) : (a + 2 * b) * (c - 240) = a * c - 240 * a + 2 * b * c - 480 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 3 * b) * (c + 241) = a * c + 241 * a + 3 * b * c + 723 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 4) * (c - 242) = a * c - 242 * a + b * c / 4 - 242 * b / 4 := by sym => simp arithSimp
example (a b c : Int) : (a + 5 * b) * (c - 243) = a * c - 243 * a + 5 * b * c - 1215 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 6 * b) * (c + 244) = a * c + 244 * a + 6 * b * c + 1464 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 2) * (c - 245) = a * c - 245 * a + b * c / 2 - 245 * b / 2 := by sym => simp arithSimp
example (a b c : Int) : (a + 3 * b) * (c - 246) = a * c - 246 * a + 3 * b * c - 738 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 4 * b) * (c + 247) = a * c + 247 * a + 4 * b * c + 988 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 5) * (c - 248) = a * c - 248 * a + b * c / 5 - 248 * b / 5 := by sym => simp arithSimp
example (a b c : Int) : (a + 6 * b) * (c - 249) = a * c - 249 * a + 6 * b * c - 1494 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 2 * b) * (c + 250) = a * c + 250 * a + 2 * b * c + 500 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 3) * (c - 251) = a * c - 251 * a + b * c / 3 - 251 * b / 3 := by sym => simp arithSimp
example (a b c : Int) : (a + 4 * b) * (c - 252) = a * c - 252 * a + 4 * b * c - 1008 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 5 * b) * (c + 253) = a * c + 253 * a + 5 * b * c + 1265 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 6) * (c - 254) = a * c - 254 * a + b * c / 6 - 254 * b / 6 := by sym => simp arithSimp
example (a b c : Int) : (a + 2 * b) * (c - 255) = a * c - 255 * a + 2 * b * c - 510 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 3 * b) * (c + 256) = a * c + 256 * a + 3 * b * c + 768 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 4) * (c - 257) = a * c - 257 * a + b * c / 4 - 257 * b / 4 := by sym => simp arithSimp
example (a b c : Int) : (a + 5 * b) * (c - 258) = a * c - 258 * a + 5 * b * c - 1290 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 6 * b) * (c + 259) = a * c + 259 * a + 6 * b * c + 1554 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 2) * (c - 260) = a * c - 260 * a + b * c / 2 - 260 * b / 2 := by sym => simp arithSimp
example (a b c : Int) : (a + 3 * b) * (c - 261) = a * c - 261 * a + 3 * b * c - 783 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 4 * b) * (c + 262) = a * c + 262 * a + 4 * b * c + 1048 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 5) * (c - 263) = a * c - 263 * a + b * c / 5 - 263 * b / 5 := by sym => simp arithSimp
example (a b c : Int) : (a + 6 * b) * (c - 264) = a * c - 264 * a + 6 * b * c - 1584 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 2 * b) * (c + 265) = a * c + 265 * a + 2 * b * c + 530 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 3) * (c - 266) = a * c - 266 * a + b * c / 3 - 266 * b / 3 := by sym => simp arithSimp
example (a b c : Int) : (a + 4 * b) * (c - 267) = a * c - 267 * a + 4 * b * c - 1068 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 5 * b) * (c + 268) = a * c + 268 * a + 5 * b * c + 1340 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 6) * (c - 269) = a * c - 269 * a + b * c / 6 - 269 * b / 6 := by sym => simp arithSimp
example (a b c : Int) : (a + 2 * b) * (c - 270) = a * c - 270 * a + 2 * b * c - 540 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 3 * b) * (c + 271) = a * c + 271 * a + 3 * b * c + 813 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 4) * (c - 272) = a * c - 272 * a + b * c / 4 - 272 * b / 4 := by sym => simp arithSimp
example (a b c : Int) : (a + 5 * b) * (c - 273) = a * c - 273 * a + 5 * b * c - 1365 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 6 * b) * (c + 274) = a * c + 274 * a + 6 * b * c + 1644 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 2) * (c - 275) = a * c - 275 * a + b * c / 2 - 275 * b / 2 := by sym => simp arithSimp
example (a b c : Int) : (a + 3 * b) * (c - 276) = a * c - 276 * a + 3 * b * c - 828 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 4 * b) * (c + 277) = a * c + 277 * a + 4 * b * c + 1108 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 5) * (c - 278) = a * c - 278 * a + b * c / 5 - 278 * b / 5 := by sym => simp arithSimp
example (a b c : Int) : (a + 6 * b) * (c - 279) = a * c - 279 * a + 6 * b * c - 1674 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 2 * b) * (c + 280) = a * c + 280 * a + 2 * b * c + 560 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 3) * (c - 281) = a * c - 281 * a + b * c / 3 - 281 * b / 3 := by sym => simp arithSimp
example (a b c : Int) : (a + 4 * b) * (c - 282) = a * c - 282 * a + 4 * b * c - 1128 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 5 * b) * (c + 283) = a * c + 283 * a + 5 * b * c + 1415 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 6) * (c - 284) = a * c - 284 * a + b * c / 6 - 284 * b / 6 := by sym => simp arithSimp
example (a b c : Int) : (a + 2 * b) * (c - 285) = a * c - 285 * a + 2 * b * c - 570 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 3 * b) * (c + 286) = a * c + 286 * a + 3 * b * c + 858 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 4) * (c - 287) = a * c - 287 * a + b * c / 4 - 287 * b / 4 := by sym => simp arithSimp
example (a b c : Int) : (a + 5 * b) * (c - 288) = a * c - 288 * a + 5 * b * c - 1440 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 6 * b) * (c + 289) = a * c + 289 * a + 6 * b * c + 1734 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 2) * (c - 290) = a * c - 290 * a + b * c / 2 - 290 * b / 2 := by sym => simp arithSimp
example (a b c : Int) : (a + 3 * b) * (c - 291) = a * c - 291 * a + 3 * b * c - 873 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 4 * b) * (c + 292) = a * c + 292 * a + 4 * b * c + 1168 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 5) * (c - 293) = a * c - 293 * a + b * c / 5 - 293 * b / 5 := by sym => simp arithSimp
example (a b c : Int) : (a + 6 * b) * (c - 294) = a * c - 294 * a + 6 * b * c - 1764 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 2 * b) * (c + 295) = a * c + 295 * a + 2 * b * c + 590 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 3) * (c - 296) = a * c - 296 * a + b * c / 3 - 296 * b / 3 := by sym => simp arithSimp
example (a b c : Int) : (a + 4 * b) * (c - 297) = a * c - 297 * a + 4 * b * c - 1188 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 5 * b) * (c + 298) = a * c + 298 * a + 5 * b * c + 1490 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 6) * (c - 299) = a * c - 299 * a + b * c / 6 - 299 * b / 6 := by sym => simp arithSimp
example (a b c : Int) : (a + 2 * b) * (c - 300) = a * c - 300 * a + 2 * b * c - 600 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 3 * b) * (c + 301) = a * c + 301 * a + 3 * b * c + 903 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 4) * (c - 302) = a * c - 302 * a + b * c / 4 - 302 * b / 4 := by sym => simp arithSimp
example (a b c : Int) : (a + 5 * b) * (c - 303) = a * c - 303 * a + 5 * b * c - 1515 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 6 * b) * (c + 304) = a * c + 304 * a + 6 * b * c + 1824 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 2) * (c - 305) = a * c - 305 * a + b * c / 2 - 305 * b / 2 := by sym => simp arithSimp
example (a b c : Int) : (a + 3 * b) * (c - 306) = a * c - 306 * a + 3 * b * c - 918 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 4 * b) * (c + 307) = a * c + 307 * a + 4 * b * c + 1228 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 5) * (c - 308) = a * c - 308 * a + b * c / 5 - 308 * b / 5 := by sym => simp arithSimp
example (a b c : Int) : (a + 6 * b) * (c - 309) = a * c - 309 * a + 6 * b * c - 1854 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 2 * b) * (c + 310) = a * c + 310 * a + 2 * b * c + 620 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 3) * (c - 311) = a * c - 311 * a + b * c / 3 - 311 * b / 3 := by sym => simp arithSimp
example (a b c : Int) : (a + 4 * b) * (c - 312) = a * c - 312 * a + 4 * b * c - 1248 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 5 * b) * (c + 313) = a * c + 313 * a + 5 * b * c + 1565 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 6) * (c - 314) = a * c - 314 * a + b * c / 6 - 314 * b / 6 := by sym => simp arithSimp
example (a b c : Int) : (a + 2 * b) * (c - 315) = a * c - 315 * a + 2 * b * c - 630 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 3 * b) * (c + 316) = a * c + 316 * a + 3 * b * c + 948 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 4) * (c - 317) = a * c - 317 * a + b * c / 4 - 317 * b / 4 := by sym => simp arithSimp
example (a b c : Int) : (a + 5 * b) * (c - 318) = a * c - 318 * a + 5 * b * c - 1590 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 6 * b) * (c + 319) = a * c + 319 * a + 6 * b * c + 1914 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 2) * (c - 320) = a * c - 320 * a + b * c / 2 - 320 * b / 2 := by sym => simp arithSimp
example (a b c : Int) : (a + 3 * b) * (c - 321) = a * c - 321 * a + 3 * b * c - 963 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 4 * b) * (c + 322) = a * c + 322 * a + 4 * b * c + 1288 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 5) * (c - 323) = a * c - 323 * a + b * c / 5 - 323 * b / 5 := by sym => simp arithSimp
example (a b c : Int) : (a + 6 * b) * (c - 324) = a * c - 324 * a + 6 * b * c - 1944 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 2 * b) * (c + 325) = a * c + 325 * a + 2 * b * c + 650 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 3) * (c - 326) = a * c - 326 * a + b * c / 3 - 326 * b / 3 := by sym => simp arithSimp
example (a b c : Int) : (a + 4 * b) * (c - 327) = a * c - 327 * a + 4 * b * c - 1308 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 5 * b) * (c + 328) = a * c + 328 * a + 5 * b * c + 1640 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 6) * (c - 329) = a * c - 329 * a + b * c / 6 - 329 * b / 6 := by sym => simp arithSimp
example (a b c : Int) : (a + 2 * b) * (c - 330) = a * c - 330 * a + 2 * b * c - 660 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 3 * b) * (c + 331) = a * c + 331 * a + 3 * b * c + 993 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 4) * (c - 332) = a * c - 332 * a + b * c / 4 - 332 * b / 4 := by sym => simp arithSimp
example (a b c : Int) : (a + 5 * b) * (c - 333) = a * c - 333 * a + 5 * b * c - 1665 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 6 * b) * (c + 334) = a * c + 334 * a + 6 * b * c + 2004 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 2) * (c - 335) = a * c - 335 * a + b * c / 2 - 335 * b / 2 := by sym => simp arithSimp
example (a b c : Int) : (a + 3 * b) * (c - 336) = a * c - 336 * a + 3 * b * c - 1008 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 4 * b) * (c + 337) = a * c + 337 * a + 4 * b * c + 1348 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 5) * (c - 338) = a * c - 338 * a + b * c / 5 - 338 * b / 5 := by sym => simp arithSimp
example (a b c : Int) : (a + 6 * b) * (c - 339) = a * c - 339 * a + 6 * b * c - 2034 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 2 * b) * (c + 340) = a * c + 340 * a + 2 * b * c + 680 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 3) * (c - 341) = a * c - 341 * a + b * c / 3 - 341 * b / 3 := by sym => simp arithSimp
example (a b c : Int) : (a + 4 * b) * (c - 342) = a * c - 342 * a + 4 * b * c - 1368 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 5 * b) * (c + 343) = a * c + 343 * a + 5 * b * c + 1715 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 6) * (c - 344) = a * c - 344 * a + b * c / 6 - 344 * b / 6 := by sym => simp arithSimp
example (a b c : Int) : (a + 2 * b) * (c - 345) = a * c - 345 * a + 2 * b * c - 690 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 3 * b) * (c + 346) = a * c + 346 * a + 3 * b * c + 1038 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 4) * (c - 347) = a * c - 347 * a + b * c / 4 - 347 * b / 4 := by sym => simp arithSimp
example (a b c : Int) : (a + 5 * b) * (c - 348) = a * c - 348 * a + 5 * b * c - 1740 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 6 * b) * (c + 349) = a * c + 349 * a + 6 * b * c + 2094 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 2) * (c - 350) = a * c - 350 * a + b * c / 2 - 350 * b / 2 := by sym => simp arithSimp
example (a b c : Int) : (a + 3 * b) * (c - 351) = a * c - 351 * a + 3 * b * c - 1053 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 4 * b) * (c + 352) = a * c + 352 * a + 4 * b * c + 1408 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 5) * (c - 353) = a * c - 353 * a + b * c / 5 - 353 * b / 5 := by sym => simp arithSimp
example (a b c : Int) : (a + 6 * b) * (c - 354) = a * c - 354 * a + 6 * b * c - 2124 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 2 * b) * (c + 355) = a * c + 355 * a + 2 * b * c + 710 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 3) * (c - 356) = a * c - 356 * a + b * c / 3 - 356 * b / 3 := by sym => simp arithSimp
example (a b c : Int) : (a + 4 * b) * (c - 357) = a * c - 357 * a + 4 * b * c - 1428 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 5 * b) * (c + 358) = a * c + 358 * a + 5 * b * c + 1790 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 6) * (c - 359) = a * c - 359 * a + b * c / 6 - 359 * b / 6 := by sym => simp arithSimp
example (a b c : Int) : (a + 2 * b) * (c - 360) = a * c - 360 * a + 2 * b * c - 720 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 3 * b) * (c + 361) = a * c + 361 * a + 3 * b * c + 1083 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 4) * (c - 362) = a * c - 362 * a + b * c / 4 - 362 * b / 4 := by sym => simp arithSimp
example (a b c : Int) : (a + 5 * b) * (c - 363) = a * c - 363 * a + 5 * b * c - 1815 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 6 * b) * (c + 364) = a * c + 364 * a + 6 * b * c + 2184 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 2) * (c - 365) = a * c - 365 * a + b * c / 2 - 365 * b / 2 := by sym => simp arithSimp
example (a b c : Int) : (a + 3 * b) * (c - 366) = a * c - 366 * a + 3 * b * c - 1098 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 4 * b) * (c + 367) = a * c + 367 * a + 4 * b * c + 1468 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 5) * (c - 368) = a * c - 368 * a + b * c / 5 - 368 * b / 5 := by sym => simp arithSimp
example (a b c : Int) : (a + 6 * b) * (c - 369) = a * c - 369 * a + 6 * b * c - 2214 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 2 * b) * (c + 370) = a * c + 370 * a + 2 * b * c + 740 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 3) * (c - 371) = a * c - 371 * a + b * c / 3 - 371 * b / 3 := by sym => simp arithSimp
example (a b c : Int) : (a + 4 * b) * (c - 372) = a * c - 372 * a + 4 * b * c - 1488 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 5 * b) * (c + 373) = a * c + 373 * a + 5 * b * c + 1865 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 6) * (c - 374) = a * c - 374 * a + b * c / 6 - 374 * b / 6 := by sym => simp arithSimp
example (a b c : Int) : (a + 2 * b) * (c - 375) = a * c - 375 * a + 2 * b * c - 750 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 3 * b) * (c + 376) = a * c + 376 * a + 3 * b * c + 1128 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 4) * (c - 377) = a * c - 377 * a + b * c / 4 - 377 * b / 4 := by sym => simp arithSimp
example (a b c : Int) : (a + 5 * b) * (c - 378) = a * c - 378 * a + 5 * b * c - 1890 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 6 * b) * (c + 379) = a * c + 379 * a + 6 * b * c + 2274 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 2) * (c - 380) = a * c - 380 * a + b * c / 2 - 380 * b / 2 := by sym => simp arithSimp
example (a b c : Int) : (a + 3 * b) * (c - 381) = a * c - 381 * a + 3 * b * c - 1143 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 4 * b) * (c + 382) = a * c + 382 * a + 4 * b * c + 1528 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 5) * (c - 383) = a * c - 383 * a + b * c / 5 - 383 * b / 5 := by sym => simp arithSimp
example (a b c : Int) : (a + 6 * b) * (c - 384) = a * c - 384 * a + 6 * b * c - 2304 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 2 * b) * (c + 385) = a * c + 385 * a + 2 * b * c + 770 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 3) * (c - 386) = a * c - 386 * a + b * c / 3 - 386 * b / 3 := by sym => simp arithSimp
example (a b c : Int) : (a + 4 * b) * (c - 387) = a * c - 387 * a + 4 * b * c - 1548 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 5 * b) * (c + 388) = a * c + 388 * a + 5 * b * c + 1940 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 6) * (c - 389) = a * c - 389 * a + b * c / 6 - 389 * b / 6 := by sym => simp arithSimp
example (a b c : Int) : (a + 2 * b) * (c - 390) = a * c - 390 * a + 2 * b * c - 780 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 3 * b) * (c + 391) = a * c + 391 * a + 3 * b * c + 1173 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 4) * (c - 392) = a * c - 392 * a + b * c / 4 - 392 * b / 4 := by sym => simp arithSimp
example (a b c : Int) : (a + 5 * b) * (c - 393) = a * c - 393 * a + 5 * b * c - 1965 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 6 * b) * (c + 394) = a * c + 394 * a + 6 * b * c + 2364 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 2) * (c - 395) = a * c - 395 * a + b * c / 2 - 395 * b / 2 := by sym => simp arithSimp
example (a b c : Int) : (a + 3 * b) * (c - 396) = a * c - 396 * a + 3 * b * c - 1188 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 4 * b) * (c + 397) = a * c + 397 * a + 4 * b * c + 1588 * b := by sym => simp arithSimp
example (a b c : Rat) : (a + b / 5) * (c - 398) = a * c - 398 * a + b * c / 5 - 398 * b / 5 := by sym => simp arithSimp
example (a b c : Int) : (a + 6 * b) * (c - 399) = a * c - 399 * a + 6 * b * c - 2394 * b := by sym => simp arithSimp
example (a b c : Nat) : (a + 2 * b) * (c + 400) = a * c + 400 * a + 2 * b * c + 800 * b := by sym => simp arithSimp
