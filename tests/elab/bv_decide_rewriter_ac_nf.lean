import Lean
/-!
# Tests for normalization up to associativity and commutativity
This file tests the `bv_ac_nf` normalization pass of `bv_decide`
-/

open Lean

/-! Now, we test the pass as part of the full `bv_normalize` procedure -/
namespace Normalize

/-- Locally override `bv_normalize` with a config that enables the acNf pass -/
local macro "bv_normalize" : tactic =>
  `(tactic| bv_normalize (config := {acNf := true, shortCircuit := true}))

/-- warning: declaration uses `sorry` -/
#guard_msgs in
theorem mul_mul_eq_mul_mul (x₁ x₂ y₁ y₂ z : BitVec 4) (h₁ : x₁ = x₂) (h₂ : y₁ = y₂) :
    x₁ * (y₁ * z) = x₂ * (y₂ * z) := by
  bv_normalize
  rename_i tgt
  guard_hyp tgt :ₛ (!!(!x₁ * y₁ == x₂ * y₂ && !z * (x₁ * y₁) == z * (x₂ * y₂))) = true
  sorry

/-- warning: declaration uses `sorry` -/
#guard_msgs in
theorem mul_eq_mul_eq_right (x y z : BitVec 64) (h : x = y) :
    x * z = y * z := by
  bv_normalize
  rename_i tgt
  guard_hyp tgt :ₛ (!!(!x == y && !z * x == z * y)) = true
  sorry

theorem add_mul_mixed (x y z : BitVec 64) :
    z * (y + x) = (y + x) * z := by
  bv_normalize

end Normalize
