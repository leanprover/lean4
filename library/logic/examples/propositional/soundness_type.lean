/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura

Define propositional calculus, valuation, provability, validity, prove soundness.

This file is based on Floris van Doorn Coq files.

Similar to soundness.lean, but defines Nc in Type.
The idea is to be able to prove soundness using recursive equations.
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

  inductive Nc : list PropF → PropF → Type :=
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

  -- Remark ⌞t⌟ indicates we should not pattern match on t.
  -- In the following lemma, we only need to pattern match on Γ ⊢ A,
  -- by pattern matching on A, we would be creating 10*6 cases instead of 10.

  lemma weakening2 : ∀ {Γ A Δ}, Γ ⊢ A → Γ ⊆ Δ → Δ ⊢ A
  | Γ ⌞A⌟     Δ (Nax Γ A Hin)          Hs := !Nax  (Hs A Hin)
  | Γ ⌞A ⇒ B⌟ Δ (ImpI Γ A B H)         Hs := !ImpI (weakening2 H (cons_sub_cons A Hs))
  | Γ ⌞B⌟     Δ (ImpE Γ A B H₁ H₂)     Hs := !ImpE (weakening2 H₁ Hs) (weakening2 H₂ Hs)
  | Γ ⌞A⌟     Δ (BotC Γ A H)           Hs := !BotC (weakening2 H (cons_sub_cons (~A) Hs))
  | Γ ⌞A ∧ B⌟ Δ (AndI Γ A B H₁ H₂)     Hs := !AndI (weakening2 H₁ Hs) (weakening2 H₂ Hs)
  | Γ ⌞A⌟     Δ (AndE₁ Γ A B H)        Hs := !AndE₁ (weakening2 H Hs)
  | Γ ⌞B⌟     Δ (AndE₂ Γ A B H)        Hs := !AndE₂ (weakening2 H Hs)
  | Γ ⌞A ∨ B⌟ Δ (OrI₁ Γ A B H)         Hs := !OrI₁ (weakening2 H Hs)
  | Γ ⌞A ∨ B⌟ Δ (OrI₂ Γ A B H)         Hs := !OrI₂ (weakening2 H Hs)
  | Γ ⌞C⌟     Δ (OrE Γ A B C H₁ H₂ H₃) Hs :=
       !OrE (weakening2 H₁ Hs) (weakening2 H₂ (cons_sub_cons A Hs)) (weakening2 H₃ (cons_sub_cons B Hs))

  lemma weakening : ∀ Γ Δ A, Γ ⊢ A → Γ++Δ ⊢ A :=
  λ Γ Δ A H, weakening2 H (sub_append_left Γ Δ)

  lemma deduction : ∀ Γ A B, Γ ⊢ A ⇒ B → A::Γ ⊢ B :=
  λ Γ A B H, !ImpE (weakening2 H (sub_cons A Γ)) (!Nax (mem_cons A Γ))

  lemma prov_impl : ∀ A B, Provable (A ⇒ B) → ∀ Γ, Γ ⊢ A → Γ ⊢ B :=
  λ A B Hp Γ Ha,
    have wHp : Γ ⊢ (A ⇒ B), from !weakening Hp,
    !ImpE wHp Ha

  lemma Satisfies_cons : ∀ {A Γ v}, Satisfies v Γ → is_true (TrueQ v A) → Satisfies v (A::Γ) :=
  λ A Γ v s t B BinAG,
    or.elim BinAG
      (λ e : B = A, by rewrite e; exact t)
      (λ i : B ∈ Γ, s _ i)

  theorem Soundness_general {v : valuation} : ∀ {A Γ}, Γ ⊢ A → Satisfies v Γ → is_true (TrueQ v A)
  | ⌞A⌟     Γ (Nax Γ A Hin) s  := s _ Hin
  | ⌞A ⇒ B⌟ Γ (ImpI Γ A B H) s :=
    by_cases
      (λ t : is_true (TrueQ v A),
        have aux₁ : Satisfies v (A::Γ), from Satisfies_cons s t,
        have aux₂ : is_true (TrueQ v B), from Soundness_general H aux₁,
        bor_inr aux₂)
      (λ f : ¬ is_true (TrueQ v A),
        have aux : bnot (TrueQ v A) = tt, by rewrite (eq_ff_of_ne_tt f),
        bor_inl aux)
  | ⌞B⌟ Γ (ImpE Γ A B H₁ H₂) s :=
    assert aux₁ : bnot (TrueQ v A) || TrueQ v B = tt, from Soundness_general H₁ s,
    assert aux₂ : TrueQ v A = tt, from Soundness_general H₂ s,
    by rewrite [aux₂ at aux₁, bnot_true at aux₁, ff_bor at aux₁]; exact aux₁
  | ⌞A⌟ Γ (BotC Γ A H) s := by_contradiction
    (λ n : TrueQ v A ≠ tt,
      assert aux₁ : TrueQ v A    = ff, from eq_ff_of_ne_tt n,
      assert aux₂ : TrueQ v (~A) = tt, begin change (bnot (TrueQ v A) || ff = tt), rewrite aux₁ end,
      have aux₃ : Satisfies v ((~A)::Γ), from Satisfies_cons s aux₂,
      have aux₄ : TrueQ v ⊥ = tt, from Soundness_general H aux₃,
      absurd aux₄ ff_ne_tt)
  | ⌞A ∧ B⌟ Γ (AndI Γ A B H₁ H₂) s :=
    have aux₁ : TrueQ v A = tt, from Soundness_general H₁ s,
    have aux₂ : TrueQ v B = tt, from Soundness_general H₂ s,
    band_intro aux₁ aux₂
  | ⌞A⌟     Γ (AndE₁ Γ A B H) s :=
    have aux : TrueQ v (A ∧ B) = tt, from Soundness_general H s,
    band_elim_left aux
  | ⌞B⌟     Γ (AndE₂ Γ A B H) s :=
    have aux : TrueQ v (A ∧ B) = tt, from Soundness_general H s,
    band_elim_right aux
  | ⌞A ∨ B⌟ Γ (OrI₁ Γ A B H) s :=
    have aux : TrueQ v A = tt, from Soundness_general H s,
    bor_inl aux
  | ⌞A ∨ B⌟ Γ (OrI₂ Γ A B H) s :=
    have aux : TrueQ v B = tt, from Soundness_general H s,
    bor_inr aux
  | ⌞C⌟     Γ (OrE Γ A B C H₁ H₂ H₃) s :=
    have aux : TrueQ v A || TrueQ v B = tt, from Soundness_general H₁ s,
    or.elim (or_of_bor_eq aux)
      (λ At : TrueQ v A = tt,
        have aux : Satisfies v (A::Γ), from Satisfies_cons s At,
        Soundness_general H₂ aux)
      (λ Bt : TrueQ v B = tt,
        have aux : Satisfies v (B::Γ), from Satisfies_cons s Bt,
        Soundness_general H₃ aux)

  theorem Soundness : Prop_Soundness :=
  λ A H v s, Soundness_general H s

end PropF
