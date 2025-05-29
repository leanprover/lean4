/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
import Init.Core
import Init.Classical

namespace Lean.Grind

/-- A helper gadget for annotating nested proofs in goals. -/
def nestedProof (p : Prop) {h : p} : p := h

/--
Gadget for marking `match`-expressions that should not be reduced by the `grind` simplifier, but the discriminants should be normalized.
We use it when adding instances of `match`-equations to prevent them from being simplified to true.

Remark: it must not be marked as `[reducible]`. Otherwise, `simp` will reduce
```
simpMatchDiscrsOnly (match 0 with | 0 => true | _ => false) = true
```
using `eq_self`.
-/
def simpMatchDiscrsOnly {α : Sort u} (a : α) : α := a

/-- Gadget for representing offsets `t+k` in patterns. -/
def offset (a b : Nat) : Nat := a + b

/-- Gadget for representing `a = b` in patterns for backward propagation. -/
def eqBwdPattern (a b : α) : Prop := a = b

/--
Gadget for representing generalization steps `h : x = val` in patterns
This gadget is used to represent patterns in theorems that have been generalized to reduce the
number of casts introduced during E-matching based instantiation.

For example, consider the theorem
```
Option.pbind_some {α1 : Type u_1} {a : α1} {α2 : Type u_2}
    {f : (a_1 : α1) → some a = some a_1 → Option α2}
    : (some a).pbind f = f a rfl
```
Now, suppose we have a goal containing the term `c.pbind g` and the equivalence class
`{c, some b}`. The E-matching module generates the instance
```
(some b).pbind (cast ⋯ g)
```
The `cast` is necessary because `g`'s type contains `c` instead of `some b.
This `cast` problematic because we don't have a systematic way of pushing casts over functions
to its arguments. Moreover, heterogeneous equality is not effective because the following theorem
is not provable in DTT:
```
theorem hcongr (h₁ : f ≍ g) (h₂ : a ≍ b)  : f a ≍ g b := ...
```
The standard solution is to generalize the theorem above and write it as
```
theorem Option.pbind_some'
        {α1 : Type u_1} {a : α1} {α2 : Type u_2}
        {x : Option α1}
        {f : (a_1 : α1) → x = some a_1 → Option α2}
        (h : x = some a)
        : x.pbind f = f a h := by
  subst h
  apply Option.pbind_some
```
Internally, we use this gadget to mark the E-matching pattern as
```
(genPattern h x (some a)).pbind f
```
This pattern is matched in the same way we match `(some a).pbind f`, but it saves the proof
for the actual term to the `some`-application in `f`, and the actual term in `x`.

In the example above, `c.pbind g` also matches the pattern `(genPattern h x (some a)).pbind f`,
and stores `c` in `x`, `b` in `a`, and the proof that `c = some b` in `h`.
-/
def genPattern {α : Sort u} (_h : Prop) (x : α) (_val : α) : α := x

/-- Similar to `genPattern` but for the heterogenous case -/
def genHEqPattern {α β : Sort u} (_h : Prop) (x : α) (_val : β) : α := x

/--
Gadget for annotating the equalities in `match`-equations conclusions.
`_origin` is the term used to instantiate the `match`-equation using E-matching.
When `EqMatch a b origin` is `True`, we mark `origin` as a resolved case-split.
-/
abbrev EqMatch (a b : α) {_origin : α} : Prop := a = b

/--
Gadget for annotating conditions of `match` equational lemmas.
We use this annotation for two different reasons:
- We don't want to normalize them.
- We have a propagator for them.
-/
abbrev MatchCond (p : Prop) : Prop := p

/--
Similar to `MatchCond`, but not reducible. We use it to ensure `simp`
will not eliminate it. After we apply `simp`, we replace it with `MatchCond`.
-/
def PreMatchCond (p : Prop) : Prop := p

theorem nestedProof_congr (p q : Prop) (h : p = q) (hp : p) (hq : q) : HEq (@nestedProof p hp) (@nestedProof q hq) := by
  subst h; apply HEq.refl

@[app_unexpander nestedProof]
def nestedProofUnexpander : PrettyPrinter.Unexpander := fun stx => do
  match stx with
  | `($_ $p:term) => `(‹$p›)
  | _ => throw ()

@[app_unexpander MatchCond]
def matchCondUnexpander : PrettyPrinter.Unexpander := fun stx => do
  match stx with
  | `($_ $p:term) => `($p)
  | _ => throw ()

@[app_unexpander EqMatch]
def eqMatchUnexpander : PrettyPrinter.Unexpander := fun stx => do
  match stx with
  | `($_ $lhs:term $rhs:term) => `($lhs = $rhs)
  | _ => throw ()

@[app_unexpander offset]
def offsetUnexpander : PrettyPrinter.Unexpander := fun stx => do
  match stx with
  | `($_ $lhs:term $rhs:term) => `($lhs + $rhs)
  | _ => throw ()

/-
Remark: `↑a` is notation for `Nat.cast a`. `Nat.cast` is an abbreviation
for `NatCast.natCast`. We added it because users wanted to use dot-notation (e.g., `a.cast`).
`grind` expands all reducible definitions. Thus, a `grind` failure state contains
many `NatCast.natCast` applications which is too verbose. We add the following
unexpander to cope with this issue.
-/
@[app_unexpander NatCast.natCast]
def natCastUnexpander : PrettyPrinter.Unexpander := fun stx => do
  match stx with
  | `($_ $a:term) => `(↑$a)
  | _ => throw ()

/--
A marker to indicate that a proposition has already been normalized and should not
be processed again.

This prevents issues when case-splitting on the condition `c` of an if-then-else
expression. Without this marker, the negated condition `¬c` might be rewritten into
an alternative form `c'`, which `grind` may not recognize as equivalent to `¬c`.
As a result, `grind` could fail to propagate that `if c then a else b` simplifies to `b`
in the `¬c` branch.
-/
def alreadyNorm (p : Prop) : Prop := p

/--
`Classical.em` variant where disjuncts are marked with `alreadyNorm` gadget.
See comment at `alreadyNorm`
-/
theorem em (p : Prop) : alreadyNorm p ∨ alreadyNorm (¬ p) :=
  Classical.em p

end Lean.Grind
