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

/-! The simp set proves the hypotheses of a conditional theorem by simplification. The hypothesis
`5 < 2 ^ 8` of `wrap_of_lt` evaluates to `True`, so `wrap 8 5` rewrites to `5`. -/

def wrap (w n : Nat) : Nat := n % 2 ^ w

@[vcgen_simp] theorem wrap_of_lt (h : n < 2 ^ w) : wrap w n = n := Nat.mod_eq_of_lt h

example : ⦃ fun _ => True ⦄ (pure (wrap 8 5) : M Nat) ⦃ fun r _ => r = 5 ⦄ := by
  vcgen

/-! `wrap_of_lt` rewrites only if its hypothesis simplifies to `True`. The hypothesis `300 < 2 ^ 3`
simplifies to `False` and `n < 2 ^ 8` simplifies to `n < 256`, so `wrap 3 300` and `wrap 8 n` stay. -/

/--
trace: case vc1
s✝ : Nat
⊢ wrap 3 300 = 300
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : ⦃ fun _ => True ⦄ (pure (wrap 3 300) : M Nat) ⦃ fun r _ => r = 300 ⦄ := by
  vcgen
  trace_state
  all_goals sorry

/--
trace: case vc1
n s✝ : Nat
⊢ wrap 8 n = n
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (n : Nat) : ⦃ fun _ => True ⦄ (pure (wrap 8 n) : M Nat) ⦃ fun r _ => r = n ⦄ := by
  vcgen
  trace_state
  all_goals sorry

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
