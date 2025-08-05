/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Rotella
-/
module

prelude
public import Lean.ErrorExplanation

public section

/--
This error occurs when attempting to project a piece of data from a proof of a proposition using an
index projection. For example, if `h` is a proof of an existential proposition, attempting to
extract the witness `h.1` is an example of this error. Such projections are disallowed because they
may violate Lean's prohibition of large elimination from `Prop` (refer to the
[Propositions](lean-manual://section/propositions) manual section for further details).

Instead of an index projection, consider using a pattern-matching `let`, `match` expression, or a
destructuring tactic like `cases` to eliminate from one propositional type to another. Note that
such elimination is only valid if the resulting value is also in `Prop`; if it is not, the error
[`lean.propRecLargeElim`](lean-manual://errorExplanation/lean.propRecLargeElim) will be raised.

# Examples

## Attempting to use index projection on existential proof

```lean broken
example (a : Nat) (h : ∃ x : Nat, x > a + 1) : ∃ x : Nat, x > 0 :=
  ⟨h.1, Nat.lt_of_succ_lt h.2⟩
```
```output
Invalid projection: Cannot project a value of non-propositional type
  Nat
from the expression
  h
which has propositional type
  ∃ x, x > a + 1
```
```lean fixed (title := "Fixed (let)")
example (a : Nat) (h : ∃ x : Nat, x > a + 1) : ∃ x : Nat, x > a :=
  let ⟨w, hw⟩ := h
  ⟨w, Nat.lt_of_succ_lt hw⟩
```
```lean (title := "Fixed (cases)")
example (a : Nat) (h : ∃ x : Nat, x > a + 1) : ∃ x : Nat, x > a := by
  cases h with
  | intro w hw =>
    exists w
    omega
```

The witness associated with a proof of an existential proposition cannot be extracted using an
index projection. Instead, it is necessary to use a pattern match: either a term like a `let`
binding or a tactic like `cases`.
-/
register_error_explanation lean.projNonPropFromProp {
  summary := "Tried to project data from a proof."
  sinceVersion := "4.23.0"
}
