import Std.WP
import Std.Tactic.Do

open Std.WP Lean.Order

set_option experimental.vcgen true

/-! The one-point rules `⨆ x, ⌜x = t⌝ ⊓ Ψ x = Ψ t` and `⨆ x, ⌜t = x⌝ ⊓ Ψ x = Ψ t` remove a
supremum whose index an equation determines. -/

example : ⦃ fun s => s = 3 ⦄ (pure () : StateM Nat Unit) ⦃ fun _ s => ⨆ n : Nat, ⌜n = s⌝ ⊓ ⌜n < 5⌝ ⦄ := by
  vcgen

example : ⦃ fun s => s = 3 ⦄ (pure () : StateM Nat Unit) ⦃ fun _ s => ⨆ n : Nat, ⌜s = n⌝ ⊓ ⌜n < 5⌝ ⦄ := by
  vcgen

example : ⦃ fun s => s = 3 ⦄ (pure () : StateM Nat Unit)
    ⦃ fun _ => ⨆ n : Nat, ⌜n = 3⌝ ⊓ (fun s => s < n + 5) ⦄ := by
  vcgen

/-! Without an equation on the index, the supremum stays. -/

/--
trace: case vc1
s✝ : Nat
⊢ iSup fun n => ⌜n < 5⌝
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : ⦃ fun s => s = 3 ⦄ (pure () : StateM Nat Unit) ⦃ fun _ _ => ⨆ n : Nat, ⌜n < 5⌝ ⦄ := by
  vcgen
  trace_state
  all_goals sorry

/-! `decide` on a literal comparison decides the branch of an `if`. -/

example : ⦃ fun _ => True ⦄ (if decide (1 < 2) then pure 3 else pure 4 : StateM Nat Nat)
    ⦃ fun r _ => r = 3 ⦄ := by
  vcgen

/-! A reflexive entailment closes. -/

example (P : Nat → Prop) : ⦃ P ⦄ (pure () : StateM Nat Unit) ⦃ fun _ => P ⦄ := by
  vcgen
