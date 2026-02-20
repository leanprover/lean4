open Lean Grind Std

set_option warn.sorry false

namespace Ex1
variable [Field Q] [LT Q] [LE Q] [LawfulOrderLT Q] [IsLinearOrder Q] [OrderedRing Q]

variable (a₁ a₂ a₃ a₄ a₅ : Q)
variable (α L ν : Q)

/--
trace: [grind.linarith.model] a₁ := 0
[grind.linarith.model] a₂ := 0
[grind.linarith.model] a₃ := 0
[grind.linarith.model] a₄ := 0
[grind.linarith.model] a₅ := 0
[grind.linarith.model] α := 0
[grind.linarith.model] L := 0
[grind.linarith.model] ν := 2
-/
#guard_msgs in
set_option trace.grind.linarith.model true in
theorem upper_bound
    (hL : L = α) (hL1 : L ≤ 1)
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (ha₃ : 0 ≤ a₃) (ha₄ : 0 ≤ a₄) (ha₅ : 0 ≤ a₅)
    (hα : α = a₁ + a₂ + a₃ + a₄ + a₅) :
    ν ≤ 9/10 := by
  fail_if_success grind
  sorry

end Ex1

namespace Ex2

variable (a₁ a₂ a₃ a₄ a₅ : Rat)
variable (α L ν : Rat)

/--
trace: [grind.linarith.model] a₁ := 0
[grind.linarith.model] a₂ := 0
[grind.linarith.model] a₃ := 0
[grind.linarith.model] a₄ := 0
[grind.linarith.model] a₅ := 0
[grind.linarith.model] α := 0
[grind.linarith.model] L := 0
[grind.linarith.model] ν := 2
-/
#guard_msgs in
set_option trace.grind.linarith.model true in
theorem upper_bound
    (hL : L = α) (hL1 : L ≤ 1)
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (ha₃ : 0 ≤ a₃) (ha₄ : 0 ≤ a₄) (ha₅ : 0 ≤ a₅)
    (hα : α = a₁ + a₂ + a₃ + a₄ + a₅) :
    ν ≤ 9/10 := by
  fail_if_success grind
  sorry

end Ex2

/--
trace: [grind.linarith.model] a := 0
[grind.linarith.model] b := 0
[grind.linarith.model] c := 0
-/
#guard_msgs in
set_option trace.grind.linarith.model true in
example [Field α] [LE α] [LT α] [Std.IsPreorder α] [OrderedRing α] (a b c : α) (h : a = b + c) : False := by
  fail_if_success grind
  sorry

/--
trace: [grind.linarith.model] a := 0
[grind.linarith.model] b := 0
[grind.linarith.model] c := 0
-/
#guard_msgs in
set_option trace.grind.linarith.model true in
example (a b c : Rat) (h : a = b + c) : False := by
  fail_if_success grind
  sorry
