/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura

Define propositional calculus, valuation, provability, validity, prove soundness.

This file is based on Floris van Doorn Coq files.

Similar to soundness.lean, but defines Nc in Type.
The idea is to be able to prove soundness using recursive equations.
-/
open nat bool list decidable

attribute [reducible]
definition PropVar := nat

inductive PropF
| Var  : PropVar → PropF
| Bot  : PropF
| Conj : PropF → PropF → PropF
| Disj : PropF → PropF → PropF
| Impl : PropF → PropF → PropF

namespace PropF
  notation `#`:max P:max := Var P
  local notation A ∨ B   := Disj A B
  local notation A ∧ B   := Conj A B
  local infixr `⇒`:27    := Impl
  notation `⊥`           := Bot

  def Neg (A)      := A ⇒ ⊥
  notation ~ A     := Neg A
  def Top          := ~⊥
  notation `⊤`     := Top
  def BiImpl (A B) := A ⇒ B ∧ B ⇒ A
  infixr `⇔`:27    := BiImpl

  def valuation   := PropVar → bool

  def TrueQ (v : valuation) : PropF → bool
  | (# P)   := v P
  | ⊥       := ff
  | (A ∨ B) := TrueQ A || TrueQ B
  | (A ∧ B) := TrueQ A && TrueQ B
  | (A ⇒ B) := bnot (TrueQ A) || TrueQ B

  attribute [reducible]
  def is_true (b : bool) := b = tt

  -- the valuation v satisfies a list of PropF, if forall (A : PropF) in Γ,
  -- (TrueQ v A) is tt (the Boolean true)
  def Satisfies (v) (Γ : list PropF) := ∀ A, A ∈ Γ → is_true (TrueQ v A)
  def Models (Γ A)                   := ∀ v, Satisfies v Γ → is_true (TrueQ v A)

  infix `⊨`:80 := Models

  def Valid (p) := [] ⊨ p
  reserve infix ` ⊢ `:26

  /- Provability -/

  inductive Nc : list PropF → PropF → Type
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

  def Provable (A) := [] ⊢ A

  def Prop_Soundness := ∀ A, Provable A → Valid A

  def Prop_Completeness := ∀ A, Valid A → Provable A

  open Nc

  lemma weakening2 : ∀ {Γ A Δ}, Γ ⊢ A → Γ ⊆ Δ → Δ ⊢ A
  | ._ ._       Δ (Nax Γ A Hin)          Hs := Nax _ _ (Hs Hin)
  | ._ .(A ⇒ B) Δ (ImpI Γ A B H)         Hs := ImpI _ _ _ (weakening2 H (cons_subset_cons A Hs))
  | ._ ._       Δ (ImpE Γ A B H₁ H₂)     Hs := ImpE _ _ _ (weakening2 H₁ Hs) (weakening2 H₂ Hs)
  | ._ ._       Δ (BotC Γ A H)           Hs := BotC _ _ (weakening2 H (cons_subset_cons (~A) Hs))
  | ._ .(A ∧ B) Δ (AndI Γ A B H₁ H₂)     Hs := AndI _ _ _ (weakening2 H₁ Hs) (weakening2 H₂ Hs)
  | ._ ._       Δ (AndE₁ Γ A B H)        Hs := AndE₁ _ _ _ (weakening2 H Hs)
  | ._ ._       Δ (AndE₂ Γ A B H)        Hs := AndE₂ _ _ _ (weakening2 H Hs)
  | ._ .(A ∨ B) Δ (OrI₁ Γ A B H)         Hs := OrI₁ _ _ _ (weakening2 H Hs)
  | ._ .(A ∨ B) Δ (OrI₂ Γ A B H)         Hs := OrI₂ _ _ _ (weakening2 H Hs)
  | ._ ._       Δ (OrE Γ A B C H₁ H₂ H₃) Hs :=
       OrE _ _ _ _ (weakening2 H₁ Hs) (weakening2 H₂ (cons_subset_cons A Hs)) (weakening2 H₃ (cons_subset_cons B Hs))

  lemma weakening : ∀ Γ Δ A, Γ ⊢ A → Γ++Δ ⊢ A :=
  λ Γ Δ A H, weakening2 H (subset_append_left Γ Δ)

  lemma deduction : ∀ Γ A B, Γ ⊢ A ⇒ B → A::Γ ⊢ B :=
  λ Γ A B H, ImpE _ _ _ (weakening2 H (subset_cons A Γ)) (Nax _ _ (mem_cons_self A Γ))

  lemma prov_impl : ∀ A B, Provable (A ⇒ B) → ∀ Γ, Γ ⊢ A → Γ ⊢ B :=
  λ A B Hp Γ Ha,
    have wHp : Γ ⊢ (A ⇒ B), from weakening _ _ _ Hp,
    ImpE _ _ _ wHp Ha

  lemma Satisfies_cons : ∀ {A Γ v}, Satisfies v Γ → is_true (TrueQ v A) → Satisfies v (A::Γ) :=
  λ A Γ v s t B BinAG,
    or.elim BinAG
      (λ e : B = A, by rewrite e; exact t)
      (λ i : B ∈ Γ, s _ i)

  attribute [simp] is_true TrueQ

  theorem Soundness_general {v : valuation} : ∀ {A Γ}, Γ ⊢ A → Satisfies v Γ → is_true (TrueQ v A)
  | ._      ._ (Nax Γ A Hin)  s  := s _ Hin
  | .(A ⇒ B) ._ (ImpI Γ A B H) s  :=
    by_cases
      (λ t : is_true (TrueQ v A),
        have Satisfies v (A::Γ), from Satisfies_cons s t,
        have TrueQ v B = tt, from Soundness_general H this,
        by simp[*])
      (λ f : ¬ is_true (TrueQ v A),
        have TrueQ v A = ff, by simp at f; simp[*],
        have bnot (TrueQ v A) = tt, by simp[*],
        by simp[*])
  | ._ ._ (ImpE Γ A B H₁ H₂) s :=
    have aux : TrueQ v A = tt, from Soundness_general H₂ s,
    have bnot (TrueQ v A) || TrueQ v B = tt, from Soundness_general H₁ s,
    by simp [aux] at this; simp[*]
  | ._ ._ (BotC Γ A H) s := by_contradiction
    (λ n : TrueQ v A ≠ tt,
      have TrueQ v A    = ff, by {simp at n; simp[*]},
      have TrueQ v (~A) = tt, begin change (bnot (TrueQ v A) || ff = tt), simp[*] end,
      have Satisfies v ((~A)::Γ), from Satisfies_cons s this,
      have TrueQ v ⊥ = tt, from Soundness_general H this,
      absurd this ff_ne_tt)
  | .(A ∧ B) ._ (AndI Γ A B H₁ H₂) s :=
    have TrueQ v A = tt, from Soundness_general H₁ s,
    have TrueQ v B = tt, from Soundness_general H₂ s,
    by simp[*]
  | ._     ._ (AndE₁ Γ A B H) s :=
    have TrueQ v (A ∧ B) = tt, from Soundness_general H s,
    by simp [TrueQ] at this; simp [*, is_true]
  | ._     ._ (AndE₂ Γ A B H) s :=
    have TrueQ v (A ∧ B) = tt, from Soundness_general H s,
    by simp at this; simp[*]
  | .(A ∨ B) ._ (OrI₁ Γ A B H) s :=
    have TrueQ v A = tt, from Soundness_general H s,
    by simp[*]
  | .(A ∨ B) ._ (OrI₂ Γ A B H) s :=
    have TrueQ v B = tt, from Soundness_general H s,
    by simp[*]
  | ._     ._ (OrE Γ A B C H₁ H₂ H₃) s :=
    have TrueQ v A || TrueQ v B = tt, from Soundness_general H₁ s,
    have or (TrueQ v A = tt) (TrueQ v B = tt), by simp at this; simp[*],
    or.elim this
      (λ At,
        have Satisfies v (A::Γ), from Satisfies_cons s At,
        Soundness_general H₂ this)
      (λ Bt,
        have Satisfies v (B::Γ), from Satisfies_cons s Bt,
        Soundness_general H₃ this)

  theorem Soundness : Prop_Soundness :=
  λ A H v s, Soundness_general H s

end PropF
