/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Std.Do.WP
meta import Std.Do.SPred.Notation

set_option linter.missingDocs true

@[expose] public section

/-!
# Hoare triples

Hoare triples form the basis for compositional functional correctness proofs about monadic programs.

As usual, `Triple x P Q` holds iff the precondition `P` entails the weakest precondition
`wp⟦x⟧ Q` of `x : m α` for the postcondition `Q`.
It is thus defined in terms of an instance `WP m ps`.
-/

namespace Std.Do

universe u v
variable {m : Type u → Type v} {ps : PostShape.{u}}

/--
A Hoare triple for reasoning about monadic programs. A Hoare triple `Triple x P Q` is a
*specification* for `x`: if assertion `P` holds before `x`, then postcondition `Q` holds after
running `x`.

`⦃P⦄ x ⦃Q⦄` is convenient syntax for `Triple x P Q`.
-/
def Triple [WP m ps] {α : Type u} (x : m α) (P : Assertion ps) (Q : PostCond α ps) : Prop :=
  P ⊢ₛ wp⟦x⟧ Q

@[inherit_doc Std.Do.Triple]
scoped syntax:lead (name := triple) "⦃" term "⦄ " term:lead " ⦃" term "⦄" : term

/--
Unexpands Hoare triples to their high-level syntax during pretty printing.
-/
@[app_unexpander Triple]
meta def unexpandTriple : Lean.PrettyPrinter.Unexpander
  | `($_ $x $P $Q) => do
    `(⦃$(← SPred.Notation.unpack P)⦄ $x ⦃$Q⦄)
  | _ => throw ()

namespace Triple

instance [WP m ps] (x : m α) : SPred.Tactic.PropAsSPredTautology (Triple x P Q) spred(P → wp⟦x⟧ Q) where
  iff := iff_of_eq (SPred.entails_true_intro P (wp⟦x⟧ Q)).symm

theorem pure [Monad m] [WPMonad m ps] {α : Type u} {Q : PostCond α ps} (a : α) (himp : P ⊢ₛ Q.1 a) :
  Triple (pure (f:=m) a) P Q := himp.trans (by simp)

theorem bind [Monad m] [WPMonad m ps] {α β : Type u} {P : Assertion ps} {Q : α → Assertion ps} {R : PostCond β ps} (x : m α) (f : α → m β)
    (hx : Triple x P (Q, R.2))
    (hf : ∀ b, Triple (f b) (Q b) R) :
    Triple (x >>= f) P R := by
  apply SPred.entails.trans hx
  simp only [WP.bind]
  apply (wp x).mono _ _
  simp only [PostCond.entails, Assertion, ExceptConds.entails.refl, and_true]
  exact hf

/--
Conjunction for two Hoare triple specifications of a program `x`.
This theorem is useful for decomposing proofs, because unrelated facts about `x` can be proven
separately and then combined with this theorem.
-/
theorem and [WP m ps] (x : m α) (h₁ : Triple x P₁ Q₁) (h₂ : Triple x P₂ Q₂) : Triple x spred(P₁ ∧ P₂) (Q₁ ∧ₚ Q₂) :=
  (SPred.and_mono h₁ h₂).trans ((wp x).conjunctive Q₁ Q₂).mpr

/--
Modus ponens for two Hoare triple specifications of a program `x`.
This theorem is useful for separating proofs. If `h₁ : Triple x P₁ Q₁` proves a basic property about
`x` and `h₂ : Triple x P₂ (Q₁ →ₚ Q₂)` is an advanced proof for `Q₂` that builds on the basic proof
for `Q₁`, then `mp x h₁ h₂` is a proof for `Q₂` about `x`.
-/
theorem mp [WP m ps] (x : m α) (h₁ : Triple x P₁ Q₁) (h₂ : Triple x P₂ (Q₁ →ₚ Q₂)) : Triple x spred(P₁ ∧ P₂) (Q₁ ∧ₚ Q₂) :=
  SPred.and_mono h₁ h₂ |>.trans ((wp x).conjunctive Q₁ (Q₁ →ₚ Q₂)).mpr |>.trans ((wp x).mono _ _ PostCond.and_imp)

end Triple
