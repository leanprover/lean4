import Std.WP

/-!
A spec precondition `fun s => have v := s * 2; ∀ b, Q () (…)` leaves the entailment
`⊤ ⊑ have v := s * 2; ∀ b, …` after the spec applies. `vcgen` substitutes `s * 2` for `v` and
continues with the program.
-/

set_option experimental.vcgen true
open Std.WP Lean.Order

abbrev M := StateM Nat

def bump : M Unit := modify (· * 2)

axiom bump_spec {Q : Unit → Nat → Prop} :
    ⦃ fun s => have v := s * 2; ∀ b : Bool, Q () (if b then v else v) ⦄ bump ⦃ Q ⦄

attribute [spec] bump_spec

example : ⦃ fun _ => True ⦄ (do bump; bump : M Unit) ⦃ fun _ s => s = s ⦄ := by
  vcgen

/--
trace: case vc1
s✝ : Nat
x✝¹ x✝ : Bool
⊢ 0 < if x✝ = true then (if x✝¹ = true then 2 else 2) * 2 else (if x✝¹ = true then 2 else 2) * 2
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : ⦃ fun s => s = 1 ⦄ (do bump; bump : M Unit) ⦃ fun _ s => 0 < s ⦄ := by
  vcgen
  trace_state
  all_goals sorry
