/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Core

namespace Lean.Grind

/-- A helper gadget for annotating nested proofs in goals. -/
def nestedProof (p : Prop) {h : p} : p := h

/--
Gadget for marking `match`-expressions that should not be reduced by the `grind` simplifier, but the discriminants should be normalized.
We use it when adding instances of `match`-equations to prevent them from being simplified to true.
-/
def simpMatchDiscrsOnly {α : Sort u} (a : α) : α := a

/-- Gadget for representing offsets `t+k` in patterns. -/
def offset (a b : Nat) : Nat := a + b

/-- Gadget for representing `a = b` in patterns for backward propagation. -/
def eqBwdPattern (a b : α) : Prop := a = b

/--
Gadget for annotating the equalities in `match`-equations conclusions.
`_origin` is the term used to instantiate the `match`-equation using E-matching.
When `EqMatch a b origin` is `True`, we mark `origin` as a resolved case-split.
-/
def EqMatch (a b : α) {_origin : α} : Prop := a = b

/--
Gadget for annotating conditions of `match` equational lemmas.
We use this annotation for two different reasons:
- We don't want to normalize them.
- We have a propagator for them.
-/
def MatchCond (p : Prop) : Prop := p

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

end Lean.Grind
