set_option grind.warning false

theorem ex1 (x y z : Nat) : x < y + z → y + 1 < z → z + x < 3*z := by
  grind

theorem ex2 {p : Prop} (x y z : Nat) : x < y + z → y + 1 < z → (p ↔ z + x < 3*z) → p := by
  grind

theorem ex3 (x y : Nat) :
    27 ≤ 13*x + 11*y → 13*x + 11*y ≤ 30 →
    7*y ≤ 9*x + 10 → 9*x ≤ 4 + 7*y → False := by
  grind

open Int.Linear Int.OfNat
#print ex1
#print ex2
#print ex3
