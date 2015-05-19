/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura

Define propositional calculus, valuation, provability, validity, prove soundness.

This file is based on Floris van Doorn Coq files.
-/
import data.nat data.list
open nat bool list decidable

definition PropVar [reducible] := nat

inductive PropF :=
| Var  : PropVar → PropF
| Bot  : PropF
| Conj : PropF → PropF → PropF
| Disj : PropF → PropF → PropF
| Impl : PropF → PropF → PropF

namespace PropF
  notation `#`:max P:max := Var P
  notation A ∨ B         := Disj A B
  notation A ∧ B         := Conj A B
  infixr `⇒`:27          := Impl
  notation `⊥`           := Bot

  definition Neg A       := A ⇒ ⊥
  notation ~ A           := Neg A
  definition Top         := ~⊥
  notation `⊤`           := Top
  definition BiImpl A B  := A ⇒ B ∧ B ⇒ A
  infixr `⇔`:27          := BiImpl

  definition valuation   := PropVar → bool

  definition TrueQ (v : valuation) : PropF → bool
  | TrueQ (# P)   := v P
  | TrueQ ⊥       := ff
  | TrueQ (A ∨ B) := TrueQ A || TrueQ B
  | TrueQ (A ∧ B) := TrueQ A && TrueQ B
  | TrueQ (A ⇒ B) := bnot (TrueQ A) || TrueQ B

  definition is_true [reducible] (b : bool) := b = tt

  -- the valuation v satisfies a list of PropF, if forall (A : PropF) in Γ,
  -- (TrueQ v A) is tt (the Boolean true)
  definition Satisfies v Γ := ∀ A, A ∈ Γ → is_true (TrueQ v A)
  definition Models Γ A    := ∀ v, Satisfies v Γ → is_true (TrueQ v A)

  infix `⊨`:80 := Models

  definition Valid p := [] ⊨ p
  reserve infix `⊢`:26

  /- Provability -/

  inductive Nc : list PropF → PropF → Prop :=
  infix ⊢ := Nc
  | Nax   : ∀ Γ A,   A ∈ Γ →             Γ ⊢ A
  | ImpI  : ∀ Γ A B, A::Γ ⊢ B →          Γ ⊢ A ⇒ B
  | ImpE  : ∀ Γ A B, Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
  | BotC  : ∀ Γ A,   (~A)::Γ ⊢ ⊥ →       Γ ⊢ A
  | AndI  : ∀ Γ A B, Γ ⊢ A → Γ ⊢ B →     Γ ⊢ A ∧ B
  | AndE₁ : ∀ Γ A B, Γ ⊢ A ∧ B →         Γ ⊢ A
  | AndE₂ : ∀ Γ A B, Γ ⊢ A ∧ B →         Γ ⊢ B
  | OrI₁  : ∀ Γ A B, Γ ⊢ A →             Γ ⊢ A ∨ B
  | OrI₂  : ∀ Γ A B, Γ ⊢ B →             Γ ⊢ A ∨ B
  | OrE   : ∀ Γ A B C, Γ ⊢ A ∨ B → A::Γ ⊢ C → B::Γ ⊢ C → Γ ⊢ C

  infix ⊢ := Nc

  definition Provable A := [] ⊢ A

  definition Prop_Soundness := ∀ A, Provable A → Valid A

  definition Prop_Completeness := ∀ A, Valid A → Provable A

  open Nc

  lemma weakening2 (Γ A) (H : Γ ⊢ A) (Δ) (Hs : Γ ⊆ Δ) : Δ ⊢ A :=
  begin
    induction H,
      state,
      exact !Nax (Hs a),
      repeat (apply sorry)
  end

end PropF
