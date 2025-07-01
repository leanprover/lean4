/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
prelude
import Std.Do.WP
import Std.Do.SPred

/-!
# Hoare triples

Hoare triples form the basis for compositional functional correctness proofs about monadic programs.

As usual, `Triple x P Q` holds iff the precondition `P` entails the weakest precondition
`wp⟦x⟧.apply Q` of `x : m α` for the postcondition `Q`.
It is thus defined in terms of an instance `WP m ps`.
-/

namespace Std.Do

universe u
variable {m : Type → Type u} {ps : PostShape}

/--
  A Hoare triple for reasoning about monadic programs.
  A proof for `Triple x P Q` is a *specification* for `x`:
  If assertion `P` holds before `x`, then postcondition `Q` holds after running `x`.

  `⦃P⦄ x ⦃Q⦄` is convenient syntax for `Triple x P Q`.
-/
def Triple [WP m ps] {α} (x : m α) (P : Assertion ps) (Q : PostCond α ps) : Prop :=
  P ⊢ₛ wp⟦x⟧ Q

@[inherit_doc Std.Do.Triple]
scoped syntax:lead (name := triple) "⦃" term "⦄ " term:lead " ⦃" term "⦄" : term

@[app_unexpander Triple]
private meta def unexpandTriple : Lean.PrettyPrinter.Unexpander
  | `($_ $x $P $Q) => do
    `(⦃$(← SPred.Notation.unpack P)⦄ $x ⦃$Q⦄)
  | _ => throw ()

namespace Triple

instance [WP m ps] (x : m α) : SPred.Tactic.PropAsSPredTautology (Triple x P Q) spred(P → wp⟦x⟧ Q) where
  iff := (SPred.entails_true_intro P (wp⟦x⟧ Q)).symm

theorem pure [Monad m] [WPMonad m ps] {α} {Q : PostCond α ps} (a : α) (himp : P ⊢ₛ Q.1 a) :
  Triple (pure (f:=m) a) P Q := himp.trans (by simp)

theorem bind [Monad m] [WPMonad m ps] {α β} {P : Assertion ps} {Q : α → Assertion ps} {R : PostCond β ps} (x : m α) (f : α → m β)
    (hx : Triple x P (Q, R.2))
    (hf : ∀ b, Triple (f b) (Q b) R) :
    Triple (x >>= f) P R := by
  apply SPred.entails.trans hx
  simp only [WP.bind]
  apply (wp x).mono _ _
  simp only [PostCond.entails, Assertion, FailConds.entails.refl, and_true]
  exact hf

theorem and [WP m ps] (x : m α) (h₁ : Triple x P₁ Q₁) (h₂ : Triple x P₂ Q₂) : Triple x spred(P₁ ∧ P₂) (Q₁ ∧ₚ Q₂) :=
  (SPred.and_mono h₁ h₂).trans ((wp x).conjunctive Q₁ Q₂).mpr

theorem rewrite_program [WP m ps] {prog₁ prog₂ : m α}
  (heq : prog₁ = prog₂) (hprf : Triple prog₂ P Q) :
  Triple prog₁ P Q := heq ▸ hprf

end Triple
