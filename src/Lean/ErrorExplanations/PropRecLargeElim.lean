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
This error occurs when attempting to eliminate a proof of a proposition into a higher type universe.
Because Lean's type theory does not allow large elimination from `Prop`, it is invalid to
pattern-match on such values—e.g., by using `let` or `match`—to produce a piece of data in a
non-propositional universe (i.e., `Type u`). More precisely, the motive of a propositional recursor
must be a proposition. (See the manual section on
[Subsingleton Elimination](lean-manual://section/subsingleton-elimination) for exceptions to this
rule.)

Note that this error will arise in any expression that eliminates from a proof into a
non-propositional universe, even if that expression occurs within another expression of
propositional type (e.g., in a `let` binding in a proof). The "Defining an intermediate data value
within a proof" example below demonstrates such an occurrence. Errors of this kind can usually be
resolved by moving the recursor application "outward," so that its motive is the proposition being
proved rather than the type of data-valued term.

# Examples

## Defining an intermediate data value within a proof

```lean broken
example {α : Type} [inst : Nonempty α] (p : α → Prop) :
    ∃ x, p x ∨ ¬ p x :=
  let val :=
    match inst with
    | .intro x => x
  ⟨val, Classical.em (p val)⟩
```
```output
Tactic `cases` failed with a nested error:
Tactic `induction` failed: recursor `Nonempty.casesOn` can only eliminate into `Prop`

α : Type
motive : Nonempty α → Sort ?u.1416
h_1 : (x : α) → motive ⋯
inst✝ : Nonempty α
⊢ motive inst✝
 after processing
  _
the dependent pattern matcher can solve the following kinds of equations
- <var> = <term> and <term> = <var>
- <term> = <term> where the terms are definitionally equal
- <constructor> = <constructor>, examples: List.cons x xs = List.cons y ys, and List.cons x xs = List.nil
```
```lean fixed
example {α : Type} [inst : Nonempty α] (p : α → Prop) :
    ∃ x, p x ∨ ¬ p x :=
  match inst with
  | .intro x => ⟨x, Classical.em (p x)⟩
```
Even though the `example` being defined has a propositional type, the body of `val` does not; it has
type `α : Type`. Thus, pattern-matching on the proof of `Nonempty α` (a proposition) to produce
`val` requires eliminating that proof into a non-propositional type and is disallowed. Instead, the
`match` expression must be moved to the top level of the `example`, where the result is a
`Prop`-valued proof of the existential claim stated in the example's header. This restructuring
could also be done using a pattern-matching `let` binding.

## Extracting the witness from an existential proof

```lean broken
def getWitness {α : Type u} {p : α → Prop} (h : ∃ x, p x) : α :=
  match h with
  | .intro x _ => x
```
```output
Tactic `cases` failed with a nested error:
Tactic `induction` failed: recursor `Exists.casesOn` can only eliminate into `Prop`

α : Type u
p : α → Prop
motive : (∃ x, p x) → Sort ?u.1419
h_1 : (x : α) → (h : p x) → motive ⋯
h✝ : ∃ x, p x
⊢ motive h✝
 after processing
  _
the dependent pattern matcher can solve the following kinds of equations
- <var> = <term> and <term> = <var>
- <term> = <term> where the terms are definitionally equal
- <constructor> = <constructor>, examples: List.cons x xs = List.cons y ys, and List.cons x xs = List.nil
```
```lean fixed (title := "Fixed (in Prop)")
-- This is `Exists.elim`
theorem useWitness {α : Type u} {p : α → Prop} {q : Prop}
    (h : ∃ x, p x) (hq : (x : α) → p x → q) : q :=
  match h with
  | .intro x hx => hq x hx
```
```lean fixed (title := "Fixed (in Type)")
def getWitness {α : Type u} {p : α → Prop}
    (h : (x : α) ×' p x) : α :=
  match h with
  | .mk x _ => x
```
In this example, simply relocating the pattern-match is insufficient; the attempted definition
`getWitness` is fundamentally unsound. (Consider the case where `p` is `fun (n : Nat) => n > 0`: if
`h` and `h'` are proofs of `∃ x, x > 0`, with `h` using witness `1` and `h'` witness `2`, then since
`h = h'` by proof irrelevance, it follows that `getWitness h = getWitness h'`—i.e., `1 = 2`.)

Instead, `getWitness` must be rewritten: either the resulting type of the function must be a
proposition (the first fixed example above), or `h` must not be a proposition (the second).

In the first corrected example, the resulting type of `useWitness` is now a proposition `q`. This
allows us to pattern-match on `h`—since we are eliminating into a propositional type—and pass the
unpacked values to `hq`. From a programmatic perspective, one can view `useWitness` as rewriting
`getWitness` in continuation-passing style, restricting subsequent computations to use its result
only to construct values in `Prop`, as required by the prohibition on propositional large
elimination. Note that `useWitness` is the existential elimination principle `Exists.elim`.

The second corrected example changes the type of `h` from an existential proposition to a
`Type`-valued dependent pair (corresponding to the `PSigma` type constructor). Since this type is
not propositional, eliminating into `α : Type u` is no longer invalid, and the previously attempted
pattern match now type-checks.
-/
register_error_explanation lean.propRecLargeElim {
  summary := "Attempted to eliminate a proof into a higher type universe."
  sinceVersion := "4.23.0"
}
