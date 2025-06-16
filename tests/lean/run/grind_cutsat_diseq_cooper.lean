set_option grind.warning false

theorem ex1 (x : Int) : 10 ≤ x → x ≤ 20 → x ≠ 11 → 11 ∣ x → False := by
  grind

theorem ex2 (x y : Int) :
    20 ≤ 2*x + y → 3*x + 2*y ≤ 38 → x ≠ 10 → 5 ∣ x → 4 ∣ y → y ≥ 4 → False := by
  grind

open Int.Linear
set_option pp.deepTerms true
#print ex1
#print ex2
