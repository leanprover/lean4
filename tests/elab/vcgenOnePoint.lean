import Std.WP
import Std.Tactic.Do

open Std.WP Lean.Order

set_option experimental.vcgen true

/-! The one-point rules remove a supremum whose index an equation determines, with the equation on
either side of `⊓`. -/

example : ⦃ fun s => s = 3 ⦄ (pure () : StateM Nat Unit) ⦃ fun _ s => ⨆ n : Nat, ⌜n = s⌝ ⊓ ⌜n < 5⌝ ⦄ := by
  vcgen

example : ⦃ fun s => s = 3 ⦄ (pure () : StateM Nat Unit) ⦃ fun _ s => ⨆ n : Nat, ⌜s = n⌝ ⊓ ⌜n < 5⌝ ⦄ := by
  vcgen

example : ⦃ fun s => s = 3 ⦄ (pure () : StateM Nat Unit) ⦃ fun _ s => ⨆ n : Nat, ⌜n < 5⌝ ⊓ ⌜n = s⌝ ⦄ := by
  vcgen

example : ⦃ fun s => s = 3 ⦄ (pure () : StateM Nat Unit) ⦃ fun _ s => ⨆ n : Nat, ⌜n < 5⌝ ⊓ ⌜s = n⌝ ⦄ := by
  vcgen

example : ⦃ fun s => s = 3 ⦄ (pure () : StateM Nat Unit)
    ⦃ fun _ => ⨆ n : Nat, ⌜n = 3⌝ ⊓ (fun s => s < n + 5) ⦄ := by
  vcgen

example : ⦃ fun s => s = 3 ⦄ (pure () : StateM Nat Unit)
    ⦃ fun _ => ⨆ n : Nat, (fun s => s < n + 5) ⊓ ⌜n = 3⌝ ⦄ := by
  vcgen

/-! At a carrier other than `Prop`, `simp` and `grind` rewrite with the lattice one-point rules. -/

example {l : Type} [CompleteLattice l] (Ψ : Nat → l) : (⨆ n, (⌜n = 3⌝ : l) ⊓ Ψ n) = Ψ 3 := by simp
example {l : Type} [CompleteLattice l] (Ψ : Nat → l) : (⨆ n, (⌜3 = n⌝ : l) ⊓ Ψ n) = Ψ 3 := by simp
example {l : Type} [CompleteLattice l] (Ψ : Nat → l) : (⨆ n, Ψ n ⊓ (⌜n = 3⌝ : l)) = Ψ 3 := by simp
example {l : Type} [CompleteLattice l] (Ψ : Nat → l) : (⨆ n, Ψ n ⊓ (⌜3 = n⌝ : l)) = Ψ 3 := by simp
example {l : Type} [CompleteLattice l] (Ψ : Nat → l) : (⨆ n, Ψ n ⊓ (⌜n = 3⌝ : l)) = Ψ 3 := by grind

/-! Without an equation on the index, the supremum stays. -/

/--
trace: case vc1
s✝ : Nat
⊢ ∃ n, n < 5
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
