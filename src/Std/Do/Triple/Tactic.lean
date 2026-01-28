/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Std.Do.Triple.Basic
meta import Std.Do.SPred.Notation

@[expose] public section

/-!
# Tactic support for Hoare triples

This module defines tactic helper theorems for applying Hoare triple specs.
It is used by the `mspec` tactic.
-/

namespace Std.Do.Triple.Tactic

universe u v
variable {m : Type u → Type v} {ps : PostShape.{u}}

theorem mspec0 {α : Type u} [WP m ps]
    {x : m α}
    {P : Assertion ps} {P' : Assertion ps}
    {Q Q' : PostCond α ps}
    (h : Triple x P' Q') (hpre : P ⊢ₛ P') (hpost : Q' ⊢ₚ Q) : P ⊢ₛ wp⟦x⟧ Q := by
  apply SPred.entails.trans hpre
  apply SPred.entails.trans (Triple.iff.mp h)
  apply (wp x).mono _ _ hpost

theorem mspec1 {α σ : Type u} [WP m (.arg σ ps)]
    {x : m α} {s : σ}
    {P : Assertion ps} {P' : Assertion (.arg σ ps)}
    {Q Q' : PostCond α (.arg σ ps)}
    (h : Triple x P' Q') (hpre : P ⊢ₛ P' s) (hpost : Q' ⊢ₚ Q) : P ⊢ₛ wp⟦x⟧ Q s := by
  apply SPred.entails.trans hpre
  apply SPred.entails.trans (Triple.iff.mp h)
  apply (wp x).mono _ _ hpost

theorem mspec2 {α σ₁ σ₂ : Type u} [WP m (.arg σ₁ (.arg σ₂ ps))]
    {x : m α} {s₁ : σ₁} {s₂ : σ₂}
    {P : Assertion ps} {P' : Assertion (.arg σ₁ (.arg σ₂ ps))}
    {Q Q' : PostCond α (.arg σ₁ (.arg σ₂ ps))}
    (h : Triple x P' Q') (hpre : P ⊢ₛ P' s₁ s₂) (hpost : Q' ⊢ₚ Q) : P ⊢ₛ wp⟦x⟧ Q s₁ s₂ := by
  apply SPred.entails.trans hpre
  apply SPred.entails.trans (Triple.iff.mp h)
  apply (wp x).mono _ _ hpost

theorem mspec3 {α σ₁ σ₂ σ₃ : Type u} [WP m (.arg σ₁ (.arg σ₂ (.arg σ₃ ps)))]
    {x : m α} {s₁ : σ₁} {s₂ : σ₂} {s₃ : σ₃}
    {P : Assertion ps} {P' : Assertion (.arg σ₁ (.arg σ₂ (.arg σ₃ ps)))}
    {Q Q' : PostCond α (.arg σ₁ (.arg σ₂ (.arg σ₃ ps)))}
    (h : Triple x P' Q') (hpre : P ⊢ₛ P' s₁ s₂ s₃) (hpost : Q' ⊢ₚ Q) : P ⊢ₛ wp⟦x⟧ Q s₁ s₂ s₃ := by
  apply SPred.entails.trans hpre
  apply SPred.entails.trans (Triple.iff.mp h)
  apply (wp x).mono _ _ hpost

theorem mspec4 {α σ₁ σ₂ σ₃ σ₄ : Type u} [WP m (.arg σ₁ (.arg σ₂ (.arg σ₃ (.arg σ₄ ps))))]
    {x : m α} {s₁ : σ₁} {s₂ : σ₂} {s₃ : σ₃} {s₄ : σ₄}
    {P : Assertion ps} {P' : Assertion (.arg σ₁ (.arg σ₂ (.arg σ₃ (.arg σ₄ ps))))}
    {Q Q' : PostCond α (.arg σ₁ (.arg σ₂ (.arg σ₃ (.arg σ₄ ps))))}
    (h : Triple x P' Q') (hpre : P ⊢ₛ P' s₁ s₂ s₃ s₄) (hpost : Q' ⊢ₚ Q) : P ⊢ₛ wp⟦x⟧ Q s₁ s₂ s₃ s₄ := by
  apply SPred.entails.trans hpre
  apply SPred.entails.trans (Triple.iff.mp h)
  apply (wp x).mono _ _ hpost

theorem mspec5 {α σ₁ σ₂ σ₃ σ₄ σ₅ : Type u} [WP m (.arg σ₁ (.arg σ₂ (.arg σ₃ (.arg σ₄ (.arg σ₅ ps)))))]
    {x : m α} {s₁ : σ₁} {s₂ : σ₂} {s₃ : σ₃} {s₄ : σ₄} {s₅ : σ₅}
    {P : Assertion ps} {P' : Assertion (.arg σ₁ (.arg σ₂ (.arg σ₃ (.arg σ₄ (.arg σ₅ ps)))))}
    {Q Q' : PostCond α (.arg σ₁ (.arg σ₂ (.arg σ₃ (.arg σ₄ (.arg σ₅ ps)))))}
    (h : Triple x P' Q') (hpre : P ⊢ₛ P' s₁ s₂ s₃ s₄ s₅) (hpost : Q' ⊢ₚ Q) : P ⊢ₛ wp⟦x⟧ Q s₁ s₂ s₃ s₄ s₅ := by
  apply SPred.entails.trans hpre
  apply SPred.entails.trans (Triple.iff.mp h) -- _ s₁ s₂ s₃ s₄ s₅
  apply (wp x).mono _ _ hpost
