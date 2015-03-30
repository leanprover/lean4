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

  lemma weakening2 : ∀ Γ A, Γ ⊢ A → ∀ Δ, Γ ⊆ Δ → Δ ⊢ A :=
  λ Γ A H, Nc.induction_on H
    (λ Γ A Hin Δ Hs,                   !Nax  (Hs A Hin))
    (λ Γ A B H w Δ Hs,                 !ImpI (w _ (cons_sub_cons A Hs)))
    (λ Γ A B H₁ H₂ w₁ w₂ Δ Hs,         !ImpE (w₁ _ Hs) (w₂ _ Hs))
    (λ Γ A H w Δ Hs,                   !BotC (w _ (cons_sub_cons (~A) Hs)))
    (λ Γ A B H₁ H₂ w₁ w₂ Δ Hs,         !AndI (w₁ _ Hs) (w₂ _ Hs))
    (λ Γ A B H w Δ Hs,                 !AndE₁ (w _ Hs))
    (λ Γ A B H w Δ Hs,                 !AndE₂ (w _ Hs))
    (λ Γ A B H w Δ Hs,                 !OrI₁ (w _ Hs))
    (λ Γ A B H w Δ Hs,                 !OrI₂ (w _ Hs))
    (λ Γ A B C H₁ H₂ H₃ w₁ w₂ w₃ Δ Hs, !OrE (w₁ _ Hs) (w₂ _ (cons_sub_cons A Hs)) (w₃ _ (cons_sub_cons B Hs)))

  lemma weakening : ∀ Γ Δ A, Γ ⊢ A → Γ++Δ ⊢ A :=
  λ Γ Δ A H, weakening2 Γ A H (Γ++Δ) (sub_append_left Γ Δ)

  lemma deduction : ∀ Γ A B, Γ ⊢ A ⇒ B → A::Γ ⊢ B :=
  λ Γ A B H, ImpE _ A _ (!weakening2 H _ (sub_cons A Γ)) (!Nax (mem_cons A Γ))

  lemma prov_impl : ∀ A B, Provable (A ⇒ B) → ∀ Γ, Γ ⊢ A → Γ ⊢ B :=
  λ A B Hp Γ Ha,
    have wHp : Γ ⊢ (A ⇒ B), from !weakening Hp,
    !ImpE wHp Ha

  lemma Satisfies_cons : ∀ {A Γ v}, Satisfies v Γ → is_true (TrueQ v A) → Satisfies v (A::Γ) :=
  λ A Γ v s t B BinAG,
    or.elim BinAG
      (λ e : B = A, by rewrite e; exact t)
      (λ i : B ∈ Γ, s _ i)

  theorem Soundness_general : ∀ A Γ, Γ ⊢ A → Γ ⊨ A :=
  λ A Γ H, Nc.induction_on H
    (λ Γ A Hin v s,   (s _ Hin))
    (λ Γ A B H r v s,
      by_cases
        (λ t : is_true (TrueQ v A),
           have aux₁ : Satisfies v (A::Γ), from Satisfies_cons s t,
           have aux₂ : is_true (TrueQ v B), from r v aux₁,
           bor_inr aux₂)
        (λ f : ¬ is_true (TrueQ v A),
           have aux : bnot (TrueQ v A) = tt, by rewrite (eq_ff_of_ne_tt f),
           bor_inl aux))
    (λ Γ A B H₁ H₂ r₁ r₂ v s,
       assert aux₁ : bnot (TrueQ v A) || TrueQ v B = tt, from r₁ v s,
       assert aux₂ : TrueQ v A = tt, from r₂ v s,
       by rewrite [aux₂ at aux₁, bnot_true at aux₁, ff_bor at aux₁]; exact aux₁)
    (λ Γ A H r v s, by_contradiction
       (λ n : TrueQ v A ≠ tt,
         assert aux₁ : TrueQ v A    = ff, from eq_ff_of_ne_tt n,
         assert aux₂ : TrueQ v (~A) = tt, begin change (bnot (TrueQ v A) || ff = tt), rewrite aux₁ end,
         have aux₃ : Satisfies v ((~A)::Γ), from Satisfies_cons s aux₂,
         have aux₄ : TrueQ v ⊥ = tt, from r v aux₃,
         absurd aux₄ ff_ne_tt))
    (λ Γ A B H₁ H₂ r₁ r₂ v s,
      have aux₁ : TrueQ v A = tt, from r₁ v s,
      have aux₂ : TrueQ v B = tt, from r₂ v s,
      band_intro aux₁ aux₂)
    (λ Γ A B H r v s,
      have aux : TrueQ v (A ∧ B) = tt, from r v s,
      band_elim_left aux)
    (λ Γ A B H r v s,
      have aux : TrueQ v (A ∧ B) = tt, from r v s,
      band_elim_right aux)
    (λ Γ A B H r v s,
      have aux : TrueQ v A = tt, from r v s,
      bor_inl aux)
    (λ Γ A B H r v s,
      have aux : TrueQ v B = tt, from r v s,
      bor_inr aux)
    (λ Γ A B C H₁ H₂ H₃ r₁ r₂ r₃ v s,
      have aux : TrueQ v A || TrueQ v B = tt, from r₁ v s,
      or.elim (or_of_bor_eq aux)
        (λ At : TrueQ v A = tt,
          have aux : Satisfies v (A::Γ), from Satisfies_cons s At,
          r₂ v aux)
        (λ Bt : TrueQ v B = tt,
          have aux : Satisfies v (B::Γ), from Satisfies_cons s Bt,
          r₃ v aux))

  theorem Soundness : Prop_Soundness :=
  λ A, Soundness_general A []

end PropF
