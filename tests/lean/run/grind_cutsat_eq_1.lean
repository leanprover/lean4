set_option grind.debug true
open Int.Linear

/--
trace: [grind.cutsat.assert] -1*「b + f a + 1」 + b + f a + 1 = 0
[grind.cutsat.assert] -1*「1」 + 1 = 0
[grind.cutsat.assert] -1*「0」 = 0
[grind.cutsat.assert] 「b + f a + 1」 = 0
-/
#guard_msgs (trace) in
set_option trace.grind.cutsat.assert true in
example (a b : Int) (f : Int → Int) (h₁ : f a + b + 3 = 2)  : False := by
  fail_if_success grind
  sorry

example (a b : Int) (_ : 2*a + 3*b = 0) (_ : 2 ∣ 3*b + 1) : False := by
  grind

example (a b : Int) (_ : 2 ∣ 3*a + 1) (_ : 2*b + 3*a = 0) : False := by
  grind

example (a b c : Int) (_ : c + 3*a = 0) (_ : 2 ∣ 3*a + 1) (_ : 2*b + c = 0) : False := by
  grind

example (a b c : Int) (_ : 2*c + 3*a = 0) (_ : 2*b + c = 0) (_ : 2 ∣ 3*a + 1) : False := by
  grind

example (a c : Int) (_ : 2*c + 3*a = 0) (_ : c + 1 = 0) : False := by
  grind

example (a c : Int) (_ : c + 3*a = 0) (_ : c + 3*a = 1) : False := by
  grind

example (a c : Int) (_ : c + 3*a = 0) (_ : c - 3*a = 6) (_ : 2*c + a = 0) : False := by
  grind

example (a b : Int) (_ : 2 ∣ a + 1) (_ : a = 2*b) : False := by
  grind

example (a b : Int) (_ : a = 2*b) (_ : 2 ∣ a + 1) : False := by
  grind

theorem ex₉ (a b c : Int) (_ : a + 2*b = 0) (_ : -c + 2*b = 0) (_ : a + c > 1) : False := by
  grind

example (a b c : Int) (_ : a + c > 1) (_ : a + 2*b = 0) (_ : -c + 2*b = 0) : False := by
  grind

example (a b c : Int) (_ : -a + -c > 1) (_ : a + 2*b = 0) (_ : -c + 2*b = 0) : False := by
  grind

example (a b c : Int) :
    -a + -c > 1 →
    a + 2*b = 0 →
    -c + 2*b = 0 → False := by
  grind

example {p : Prop} (a c : Int) :
        a + 2*c > 10 →
        p ∨ [a + c] = [5 - c] →
        ¬p →
        False := by
  grind

example (a : Int) : a > 2 → a = 0 → False := by
  grind

example (a b : Int) : a = 0 → b = 1 → a + b > 2 → False := by
  grind

example (a b c : Int) : a = 0 → a + b > 2 → b = c → 1 = c → False := by
  grind

example (p : Int) (n : Nat) (hmp : Int.negSucc (n + 1) + 1 = p)
    (hnm : Int.negSucc (n + 1 + 1) + 1 = Int.negSucc (n + 1)) : p = Int.negSucc n := by
  grind
