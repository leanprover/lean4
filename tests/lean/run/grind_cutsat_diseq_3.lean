set_option grind.warning false
set_option grind.debug true
open Int.Linear

theorem ex₁ (a b c : Int) : c ≥ 0 → b ≥ 0 → 1 ≤ a + c → a + b ≤ 1 → a ≠ 1 → c ≤ a → False := by
  grind

#print ex₁
