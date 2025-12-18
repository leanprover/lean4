module

example (x y : Int) :
    27 ≤ 11*x + 13*y →
    11*x + 13*y ≤ 45 →
    -10 ≤ 7*x - 9*y →
    7*x - 9*y ≤ 4 → False := by
  -- `omega` fails in this example
  grind

example (x : Int) : 100 ≤ x → x ≤ 10000 → 20000 ∣ 3*x → False := by
  grind

abbrev problem₁ [∀ n, OfNat α n] [Neg α] [Mul α] [Sub α] [Add α] [LE α] (x y : α) : Prop :=
  27 ≤ 11*x + 13*y ∧
  11*x + 13*y ≤ 45 ∧
  -10 ≤ 7*x - 9*y ∧
  7*x - 9*y ≤ 4

/--
trace: [grind.lia.model] x := 241/154
[grind.lia.model] y := 1
-/
#guard_msgs (trace) in
set_option trace.grind.lia.model true in
example (x y : Int) : problem₁ x y → False := by
  fail_if_success grind +qlia -- Rational counterexamples allowed
  sorry

/-- info: true -/
#guard_msgs in
open Std.Internal in
#eval problem₁ (241/154 : Rat) (1 : Rat)

theorem ex₁ (x y : Int) :
    27 ≤ 13*x + 11*y → 13*x + 11*y ≤ 30 →
    -10 ≤ 9*x - 7*y → 9*x - 7*y ≤ 4 → False := by
  grind

theorem ex₂ (x y : Int) :
    27 ≤ 11*x + 13*y → 11*x + 13*y ≤ 45 →
    -10 ≤ 7*x - 9*y → 7*x - 9*y ≤ 4 → False := by
  grind

theorem ex₃ (x y : Int) :
    5 ≤ x + y → x + 2*y ≤ 14 → 7 ∣ x → 4 ∣ y → y ≥ 4 → False := by
  grind

theorem ex₄ (x y : Int) :
    5 ≤ 2*x + y → 3*x + 2*y ≤ 14 → 7 ∣ x → 4 ∣ y → y ≥ 4 → False := by
  grind

theorem ex₅ (x y : Int) : 1 ≤ x + y → 100 ∣ x + y → 100 ≤ x + y := by
  grind

open Int.Linear
#print ex₁
#print ex₂
#print ex₃
#print ex₄
#print ex₅
