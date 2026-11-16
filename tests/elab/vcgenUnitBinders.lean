import Std.WP

/-!
`vcgen` introduces no local for a binder over a type with one constructor and no fields, such as
`Unit` or `True`, and substitutes the constructor for the binder.
-/

open Std.WP Lean.Order
set_option experimental.vcgen true

abbrev M := StateM Nat

/--
trace: case vc1
G : PUnit → True → Nat → Prop
n✝ s✝ : Nat
⊢ G PUnit.unit True.intro n✝
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (G : Unit → True → Nat → Prop) :
    ∀ (u : Unit) (h : True) (n : Nat), ⦃ fun _ => True ⦄ (pure n : M Nat) ⦃ fun r _ => G u h r ⦄ := by
  vcgen
  trace_state
  all_goals sorry

/-! A binder whose type mentions a unit binder mentions the constructor. -/

/--
trace: case vc1
G : Nat → Prop
a✝ : PUnit.unit = PUnit.unit
n✝ s✝ : Nat
⊢ G n✝
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (G : Nat → Prop) :
    ∀ (u : Unit), u = () → ∀ n : Nat, ⦃ fun _ => True ⦄ (pure n : M Nat) ⦃ fun r _ => G r ⦄ := by
  vcgen -simp
  trace_state
  all_goals sorry

/-! The proof term passes the kernel. -/

example : ∀ (u : Unit) (h : True) (n : Nat), ⦃ fun _ => True ⦄ (pure (u, n) : M (Unit × Nat))
    ⦃ fun r _ => r = (u, n) ∧ (h = h) ⦄ := by
  vcgen
