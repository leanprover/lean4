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

example (a b c : Nat) : Int.ofNat (a + b) = 0 → a + b + b ≤ c → b ≤ c := by
  grind

example (a b c : Nat) : Int.ofNat (a + b) = 0 → a + b + b ≤ c → Int.ofNat b ≤ c := by
  grind

example (a b c : Nat) : a + b < c → c ≥ 0 := by
  grind

example (a b : Int) : a + b = Int.ofNat 2 → a - 2 = -b := by
  grind

/--
info: [grind.cutsat.assert] -1*「↑a * ↑b」 ≤ 0
[grind.cutsat.assert] -1*↑c ≤ 0
[grind.cutsat.assert] -1*↑c + 「↑a * ↑b」 + 1 ≤ 0
[grind.cutsat.assert] ↑c = 0
[grind.cutsat.assert] 0 ≤ 0
[grind.cutsat.assert] 「↑a * ↑b」 + 1 ≤ 0
[grind.cutsat.assert] 1 ≤ 0
-/
#guard_msgs (info) in
set_option trace.grind.cutsat.assert true in
example (a b c : Nat) : c > a * b → c >= 1 := by
  grind
