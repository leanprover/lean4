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

theorem ex₆ (a b : Int) : 3 ≤ a + b → b + a ≠ 3 → a ≠ 4 - b → a ≠ 5 - b → a ≠ -b + 6 → b + a ≠ 7 → a + b ≠ 8 → b + a < 9 → False := by
  grind

example (a b : Int) :
     b + a < 8 →
     3 ≤ a + b →
     b + a ≠ 3 →
     a ≠ 4 - b →
     a ≠ 5 - b →
     a ≠ -b + 6 →
     b + a ≠ 7 → False := by
  grind

#print ex₁
#print ex₂
#print ex₃
#print ex₄
#print ex₅
#print ex₆

example (a : Int) : 1 ≤ a → a ≠ 1 → a ≤ 2 → a ≠ 2 → False := by
  grind

example (a : Int) : 1 ≤ a → a ≤ 2 → a ≠ 1 → a ≠ 2 → False := by
  grind

example (a : Int) : a ≠ 2 → 1 ≤ a → a ≤ 2 → a ≠ 1 → False := by
  grind

example (a : Int) : a ≠ 1 → a ≠ 2 → 1 ≤ a → a ≤ 2 → False := by
  grind
