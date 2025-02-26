set_option grind.warning false
set_option grind.debug true
open Int.Linear

theorem ex₁ (a b c : Int) : a + 2*b = 0 → c + b = -b → a = c := by
  grind

theorem ex₂ (a b c : Int) : a + 2*b = 0 → a = c → c + b = -b := by
  grind

theorem ex₃ (a b c : Int) : a + b + c = 0 → a = c → b = 4 → c = -2 := by
  grind

/--
info: [grind.cutsat.assert] a + -2*b + -2*c = 0
[grind.cutsat.assert] a + -2*b + -2*d ≠ 0
[grind.cutsat.diseq] d + -1*c ≠ 0
[grind.cutsat.assert] -1*d + c = 0
[grind.cutsat.assert] 0 ≠ 0
-/
#guard_msgs (info) in
set_option trace.grind.cutsat.assert true in
set_option trace.grind.cutsat.diseq true in
theorem ex₄ (a b c d : Int) : a = 2*b + 2*c → a - 2*b - 2*d ≠ 0 → c ≠ d := by
  grind

theorem ex₅ (a b c : Int) : c = a → a + b ≤ 3 → 2 < b + c → a + b = 3 := by
  grind

#print ex₁
#print ex₂
#print ex₃
#print ex₄
#print ex₅
