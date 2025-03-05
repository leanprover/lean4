import Std.Internal.Rat
set_option grind.warning false

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
info: [grind.cutsat.model] x := 241/154
[grind.cutsat.model] y := 1
-/
#guard_msgs (info) in
set_option trace.grind.cutsat.model true in
example (x y : Int) : problem₁ x y → False := by
  fail_if_success grind +qlia
  sorry

/-- info: true -/
#guard_msgs (info) in
open Std.Internal in
#eval problem₁ (241/154 : Rat) (1 : Rat)
