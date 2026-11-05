import Std.WP

/-!
A spec precondition `fun s => have v := e; P v` leaves the entailment `⊤ ⊑ have v := e; P v` after
the spec applies. `vcgen` handles the `have` as `wpLet?` handles a `let` in the program: it
simplifies the value, substitutes a duplicable value such as a literal, and introduces any other
value as a local definition, then continues with the program.
-/

set_option experimental.vcgen true
open Std.WP Lean.Order

abbrev M := StateM Nat

def bump : M Unit := modify (· * 2)

def keep : M Unit := modify id

axiom bump_spec {Q : Unit → Nat → Prop} :
    ⦃ fun s => have v := s * 2; ∀ b : Bool, Q () (if b then v else v) ⦄ bump ⦃ Q ⦄

axiom keep_spec {Q : Unit → Nat → Prop} :
    ⦃ fun s => have v := s; ∀ b : Bool, Q () (if b then v else v) ⦄ keep ⦃ Q ⦄

attribute [spec] bump_spec keep_spec

example : ⦃ fun _ => True ⦄ (do bump; bump : M Unit) ⦃ fun _ s => s = s ⦄ := by
  vcgen

/-! The first value `1 * 2` simplifies to the literal `2`, so `vcgen` substitutes it. The second
value `(if b then 2 else 2) * 2` is not duplicable, so `vcgen` introduces it. -/

/--
trace: case vc1
s✝ : Nat
x✝¹ : Bool
v : Nat := (if x✝¹ = true then 2 else 2) * 2
x✝ : Bool
⊢ 0 < if x✝ = true then v else v
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : ⦃ fun s => s = 1 ⦄ (do bump; bump : M Unit) ⦃ fun _ s => 0 < s ⦄ := by
  vcgen
  trace_state
  all_goals sorry

/-! The value `s` becomes the literal `1`, so `vcgen` substitutes it. -/

/--
trace: case vc1
s✝ : Nat
x✝ : Bool
⊢ 0 < if x✝ = true then 1 else 1
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : ⦃ fun s => s = 1 ⦄ (keep : M Unit) ⦃ fun _ s => 0 < s ⦄ := by
  vcgen
  trace_state
  all_goals sorry
