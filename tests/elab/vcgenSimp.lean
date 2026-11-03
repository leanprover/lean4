import Std.WP

/-!
`vcgen` rewrites hypotheses, state arguments and verification conditions with its simp set: the
`@[vcgen_simp]` theorems, the theorems of the `simp [...]` clause, and the evaluation of ground
terms. `vcgen -simp` turns the rewriting off.
-/

open Std.WP Lean.Order
set_option experimental.vcgen true

abbrev M := StateM Nat

/-! The split on `"a" = "b"` leaves the hypothesis `"a" = "b"`, which evaluates to `False`. -/

example : ⦃ fun _ => True ⦄ (if "a" = "b" then pure 1 else pure 2 : M Nat) ⦃ fun r _ => r = 2 ⦄ := by
  vcgen

/--
trace: case vc1
s✝ : Nat
h✝ : "a" = "b"
⊢ 1 = 2
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : ⦃ fun _ => True ⦄ (if "a" = "b" then pure 1 else pure 2 : M Nat) ⦃ fun r _ => r = 2 ⦄ := by
  vcgen -simp
  trace_state
  all_goals sorry

/-! Ground evaluation turns the verification condition `"x" = "x" ∨ "x" = "y"` into `True ∨ False`,
which the `@[vcgen_simp]` theorem `true_or` rewrites to `True`. -/

example : ⦃ fun _ => True ⦄ (pure "x" : M String) ⦃ fun r _ => r = "x" ∨ r = "y" ⦄ := by
  vcgen

/-! `decide` on a literal comparison decides the branch of an `if`. -/

example : ⦃ fun _ => True ⦄ (if decide (1 < 2) then pure 3 else pure 4 : M Nat) ⦃ fun r _ => r = 3 ⦄ := by
  vcgen

/-! A reflexive entailment closes. -/

example (P : Nat → Prop) : ⦃ P ⦄ (pure () : M Unit) ⦃ fun _ => P ⦄ := by
  vcgen

/-! Index elimination removes a supremum whose index an equation determines, with the equation on
either side of `⊓`. -/

example : ⦃ fun s => s = 3 ⦄ (pure () : M Unit) ⦃ fun _ s => ⨆ n : Nat, ⌜n = s⌝ ⊓ ⌜n < 5⌝ ⦄ := by
  vcgen

example : ⦃ fun s => s = 3 ⦄ (pure () : M Unit) ⦃ fun _ s => ⨆ n : Nat, ⌜s = n⌝ ⊓ ⌜n < 5⌝ ⦄ := by
  vcgen

example : ⦃ fun s => s = 3 ⦄ (pure () : M Unit) ⦃ fun _ s => ⨆ n : Nat, ⌜n < 5⌝ ⊓ ⌜n = s⌝ ⦄ := by
  vcgen

example : ⦃ fun s => s = 3 ⦄ (pure () : M Unit) ⦃ fun _ s => ⨆ n : Nat, ⌜n < 5⌝ ⊓ ⌜s = n⌝ ⦄ := by
  vcgen

example : ⦃ fun s => s = 3 ⦄ (pure () : M Unit) ⦃ fun _ => ⨆ n : Nat, ⌜n = 3⌝ ⊓ (fun s => s < n + 5) ⦄ := by
  vcgen

example : ⦃ fun s => s = 3 ⦄ (pure () : M Unit) ⦃ fun _ => ⨆ n : Nat, (fun s => s < n + 5) ⊓ ⌜n = 3⌝ ⦄ := by
  vcgen

/-! Without an equation on the index, the supremum becomes an `∃`. -/

/--
trace: case vc1
s✝ : Nat
⊢ ∃ n, n < 5
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : ⦃ fun s => s = 3 ⦄ (pure () : M Unit) ⦃ fun _ _ => ⨆ n : Nat, ⌜n < 5⌝ ⦄ := by
  vcgen
  trace_state
  all_goals sorry

/-! The state argument `0 + s` rewrites to `s` with the clause theorem `Nat.zero_add`. -/

/--
trace: case vc1
s✝ : Nat
⊢ s✝ = s✝ + 1
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : ⦃ fun _ => True ⦄ (do modify (0 + ·); get : M Nat) ⦃ fun r s => r = s + 1 ⦄ := by
  vcgen simp [Nat.zero_add]
  trace_state
  all_goals sorry

/-! The clause takes local hypotheses, proof terms and `*`. -/

opaque f : Nat → Nat

example (h : f 3 = 5) : ⦃ fun _ => True ⦄ (pure (f 3) : M Nat) ⦃ fun r _ => r = 5 ⦄ := by
  vcgen simp [h]

example (h : f 3 = 5) : ⦃ fun _ => True ⦄ (pure (f 3) : M Nat) ⦃ fun r _ => r = 5 ⦄ := by
  vcgen simp [show f 3 = 5 from h]

example (h : f 3 = 5) : ⦃ fun _ => True ⦄ (pure (f 3) : M Nat) ⦃ fun r _ => r = 5 ⦄ := by
  vcgen simp [*]

/-! A theorem tagged `@[vcgen_simp]` is in the simp set of every `vcgen` call. -/

def g (n : Nat) : Nat := 0 + n

@[vcgen_simp] theorem g_eq (n : Nat) : g n = n := Nat.zero_add n

example (n : Nat) : ⦃ fun _ => True ⦄ (pure (g n) : M Nat) ⦃ fun r _ => r = n ⦄ := by
  vcgen

/-! A `simp` tactic on the next line is not part of the `vcgen` call. -/

example (n : Nat) : ⦃ fun _ => True ⦄ (pure (0 + n) : M Nat) ⦃ fun r _ => r = n ⦄ := by
  vcgen
  simp

/-! Errors. -/

/-- error: `vcgen simp [...]` conflicts with the config option `simp := false` -/
#guard_msgs in
example : ⦃ fun _ => True ⦄ (pure 1 : M Nat) ⦃ fun r _ => r = 1 ⦄ := by
  vcgen -simp simp [Nat.add_zero]

/-- error: `vcgen simp [...]` cannot erase a theorem -/
#guard_msgs in
example : ⦃ fun _ => True ⦄ (pure 1 : M Nat) ⦃ fun r _ => r = 1 ⦄ := by
  vcgen simp [-Nat.add_zero]
