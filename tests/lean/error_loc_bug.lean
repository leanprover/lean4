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

  reserve infix ` ⊢ `:26

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
  | Γ ⌞A ∧ B⌟ Δ (OrI₁ Γ A B H)         Hs := !OrI₁ (weakening2 H Hs)
  | Γ ⌞A ∨ B⌟ Δ (OrI₂ Γ A B H)         Hs := !OrI₂ (weakening2 H Hs)
  | Γ ⌞C⌟     Δ (OrE Γ A B C H₁ H₂ H₃) Hs :=
       !OrE (weakening2 H₁ Hs) (weakening2 H₂ (cons_sub_cons A Hs)) (weakening2 H₃ (cons_sub_cons B Hs))

end PropF
