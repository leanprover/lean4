/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob Simmons
-/
module

prelude
public import Lean.ErrorExplanation
meta import Lean.ErrorExplanation

/--
Tactic-based proofs using induction in Lean need to use a pattern-matching-like notation to describe
individual cases of the proof. However, the `induction'` tactic in Mathlib and the specialized
`induction` tactic for natural numbers used in the Natural Number Game follows a different pattern.

# Examples

## Adding Explicit Cases to an Induction Proof

```lean broken
theorem zero_mul (m : Nat) : 0 * m = 0 := by
  induction m with n n_ih
  rw [Nat.mul_zero]
  rw [Nat.mul_succ]
  rw [Nat.add_zero]
  rw [n_ih]
```
```output
unknown tactic
```
```lean fixed
theorem zero_mul (m : Nat) : 0 * m = 0 := by
  induction m with
  | zero =>
    rw [Nat.mul_zero]
  | succ n n_ih =>
    rw [Nat.mul_succ]
    rw [Nat.add_zero]
    rw [n_ih]
```
The broken example has the structure of a correct proof in the Natural Numbers Game, and this
proof will work if you `import Mathlib` and replace `induction` with `induction'`. Induction tactics
in basic Lean expect the `with` keyword to be followed by a series of cases, and the names for
the inductive case are provided in the `succ` case rather than being provided up-front.

-/
register_error_explanation lean.inductionWithNoAlts {
  summary := "Induction pattern with nontactic in natural-number-game-style `with` clause."
  sinceVersion := "4.26.0"
}
