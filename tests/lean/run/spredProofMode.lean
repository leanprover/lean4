/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
import Lean.Elab.Tactic.Do
import Std.Do

open Std.Do

variable (σs : List Type)

theorem start_stop (Q : SPred σs) (H : Q ⊢ₛ Q) : Q ⊢ₛ Q := by
  mstart
  mintro HQ
  mstop
  exact H

theorem exact (Q : SPred σs) : Q ⊢ₛ Q := by
  mstart
  mintro HQ
  mexact HQ

theorem exact_pure (P Q : SPred σs) (hP : ⊢ₛ P): Q ⊢ₛ P := by
  mintro _
  mexact hP

theorem clear (P Q : SPred σs) : P ⊢ₛ Q → Q := by
  mintro HP
  mintro HQ
  mclear HP
  mexact HQ

theorem assumption (P Q : SPred σs) : Q ⊢ₛ P → Q := by
  mintro _ _
  massumption

theorem assumption_pure (P Q : SPred σs) (hP : ⊢ₛ P): Q ⊢ₛ P := by
  mintro _
  massumption

namespace pure

theorem move (Q : SPred σs) (ψ : φ → ⊢ₛ Q): ⌜φ⌝ ⊢ₛ Q := by
  mintro Hφ
  mpure Hφ
  mexact (ψ Hφ)

theorem move_multiple (Q : SPred σs) : ⌜φ₁⌝ ⊢ₛ ⌜φ₂⌝ → Q → Q := by
  mintro Hφ1
  mintro Hφ2
  mintro HQ
  mpure Hφ1
  mpure Hφ2
  mexact HQ

theorem move_conjunction (Q : SPred σs) : (⌜φ₁⌝ ∧ ⌜φ₂⌝) ⊢ₛ Q → Q := by
  mintro Hφ
  mintro HQ
  mpure Hφ
  mexact HQ

end pure

namespace pureintro

theorem simple : ⊢ₛ (⌜True⌝ : SPred σs) := by
  mpure_intro
  exact True.intro

theorem or : ⊢ₛ ⌜True⌝ ∨ (⌜False⌝ : SPred σs) := by
  mpure_intro
  left
  exact True.intro

theorem with_proof (H : A → B) (P Q : SPred σs) : P ⊢ₛ Q → ⌜A⌝ → ⌜B⌝ := by
  mintro _HP _HQ
  mpure_intro
  exact H

end pureintro

namespace frame

theorem move (P Q : SPred σs) : ⊢ₛ ⌜p⌝ ∧ Q ∧ ⌜q⌝ ∧ ⌜r⌝ ∧ P ∧ ⌜s⌝ ∧ ⌜t⌝ → Q := by
  mintro _
  mframe
  mcases h with hP
  mexact h

theorem move_multiple (P Q : SPred σs) : ⊢ₛ ⌜p⌝ ∧ Q ∧ ⌜q⌝ ∧ ⌜r⌝ ∧ P ∧ ⌜s⌝ ∧ ⌜t⌝ → Q := by
  mintro h
  mcases h with ⟨hp, hQ, hq, rest⟩
  mframe
  mexact hQ

end frame

theorem revert (P Q R : SPred σs) : P ∧ Q ∧ R ⊢ₛ R := by
  mintro ⟨HP, HQ, HR⟩
  mrevert HR
  mrevert HP
  mintro HP'
  mintro HR'
  mexact HR'

namespace constructor

theorem and (Q : SPred σs) : Q ⊢ₛ Q ∧ Q := by
  mintro HQ
  mconstructor <;> mexact HQ

end constructor

theorem exfalso (P : SPred σs) : ⌜False⌝ ⊢ₛ P := by
  mintro HP
  mexfalso
  mexact HP

namespace leftright

theorem left (P Q : SPred σs) : P ⊢ₛ P ∨ Q := by
  mintro HP
  mleft
  mexact HP

theorem right (P Q : SPred σs) : Q ⊢ₛ P ∨ Q := by
  mintro HQ
  mright
  mexact HQ

theorem complex (P Q R : SPred σs) : ⊢ₛ P → Q → P ∧ (R ∨ Q ∨ R) := by
  mintro HP HQ
  mconstructor
  · massumption
  mright
  mleft
  mexact HQ

end leftright

namespace specialize

theorem simple (P Q : SPred σs) : P ⊢ₛ (P → Q) → Q := by
  mintro HP HPQ
  mspecialize HPQ HP
  mexact HPQ

theorem multiple (P Q R : SPred σs) : ⊢ₛ P → Q → (P → Q → R) → R := by
  mintro HP HQ HPQR
  mspecialize HPQR HP HQ
  mexact HPQR

theorem pure_imp (P Q R : SPred σs) : (⊢ₛ P) → ⊢ₛ Q → (P → Q → R) → R := by
  intro HP
  mintro HQ HPQR
  mspecialize HPQR HP HQ
  mexact HPQR

theorem forall' (y : Nat) (Q : Nat → SPred σs) : ⊢ₛ (∀ x, Q x) → Q (y + 1) := by
  mintro HQ
  mspecialize HQ (y + 1)
  mexact HQ

theorem mixed (y : Nat) (P Q : SPred σs) (Ψ : Nat → SPred σs) (hP : ⊢ₛ P) : ⊢ₛ Q → (∀ x, P → Q → Ψ x) → Ψ (y + 1) := by
  mintro HQ HΨ
  mspecialize HΨ (y + 1) hP HQ
  mexact HΨ

theorem pure_mixed (y : Nat) (P Q : SPred σs) (Ψ : Nat → SPred σs) (hP : ⊢ₛ P) (hΨ : ∀ x, ⊢ₛ P → Q → Ψ x) : ⊢ₛ Q → Ψ (y + 1) := by
  mintro HQ
  mspecialize_pure (hΨ (y + 1)) hP HQ => HΨ
  mexact HΨ

theorem pure_with_local (P : SPred σs) (hc : c) : (⌜c⌝ → P) ⊢ₛ P := by
  mintro HP
  mspecialize HP hc
  mexact HP

end specialize

namespace havereplace

theorem mrepl (P Q : SPred σs) : P ⊢ₛ (P → Q) → Q := by
  mintro HP HPQ
  mreplace HPQ : Q := by mspecialize HPQ HP; mexact HPQ
  mexact HPQ

theorem mhave (P Q : SPred σs) : P ⊢ₛ (P → Q) → Q := by
  mintro HP HPQ
  mhave HQ : Q := by mspecialize HPQ HP; mexact HPQ
  mhave HQ := by mspecialize HPQ HP; mexact HPQ
  mexact HQ

theorem mixed (y : Nat) (P Q : SPred σs) (Ψ : Nat → SPred σs) (hP : ⊢ₛ P) : ⊢ₛ Q → (∀ x, P → Q → Ψ x) → Ψ (y + 1) := by
  mintro HQ HΨ
  mhave H := by mspecialize HΨ (y + 1) hP HQ; mexact HΨ
  mexact H

end havereplace

namespace cases

theorem rename (P : SPred σs) : P ⊢ₛ P := by
  mintro HP
  mcases HP with HP'
  mexact HP'

theorem clear (P Q : SPred σs) : ⊢ₛ P → Q → P := by
  mintro HP HQ
  mcases HQ with -
  mexact HP

theorem pure (P : SPred σs) (Q : Prop) : φ → (⊢ₛ P → ⌜Q⌝ → P) := by
  intro hφ
  mintro HP HQ
  mcases HQ with ⌜hQ⌝
  mexact HP

theorem pure_exact (P : SPred σs) (Q : Prop) (hqr : Q → ⊢ₛ R) : ⊢ₛ P → ⌜Q⌝ → R := by
  mintro HP HQ
  mcases HQ with ⌜hQ⌝
  mexact hqr hQ

theorem and (P Q R : SPred σs) : (P ∧ Q ∧ R) ⊢ₛ R := by
  mintro HPQR
  mcases HPQR with ⟨HP, HQ, HR⟩
  mexact HR

theorem and_clear_pure (P Q R : SPred σs) (φ : Prop) : (P ∧ Q ∧ ⌜φ⌝ ∧ R) ⊢ₛ R := by
  mintro HPQR
  mcases HPQR with ⟨_, -, ⌜hφ⌝, HR⟩
  mexact HR

theorem or (P Q R : SPred σs) : P ∧ (Q ∨ R) ∧ (Q → R) ⊢ₛ R := by
  mintro H
  mcases H with ⟨-, ⟨HQ | HR⟩, HQR⟩
  · mspecialize HQR HQ
    mexact HQR
  · mexact HR

theorem and_persistent (P Q R : SPred σs) : (P ∧ Q ∧ R) ⊢ₛ R := by
  mintro HPQR
  mcases HPQR with ⟨#HP, HQ, □HR⟩
  mexact HR

theorem and_pure (P Q R : Prop) : (⌜P⌝ ∧ ⌜Q⌝ ∧ ⌜R⌝) ⊢ₛ (⌜R⌝ : SPred σs) := by
  mintro HPQR
  mcases HPQR with ⟨%HP, ⌜HQ⌝, HR⟩
  mpure_intro
  exact HR

end cases

namespace introforall

theorem beta_conj (P Q R : SPred (Nat::σs)) (H : ∀ n, P n ∧ Q n ⊢ₛ R n) : P ∧ Q ⊢ₛ R := by
  mintro ⟨HP, HQ⟩ ∀s
  mstop
  exact H s

end introforall

namespace refine

theorem and (P Q R : SPred σs) : (P ∧ Q ∧ R) ⊢ₛ P ∧ R := by
  mintro ⟨HP, HQ, HR⟩
  mrefine ⟨HP, HR⟩

theorem exists_1 (ψ : Nat → SPred σs) : ψ 42 ⊢ₛ ∃ x, ψ x := by
  mintro H
  mrefine ⟨⌜42⌝, H⟩

theorem exists_2 (ψ : Nat → SPred σs) : ψ 42 ⊢ₛ ∃ x, ψ x := by
  mintro H
  mexists 42

end refine

theorem mosel1 {α : Type} (P : SPred σs) (Φ Ψ : α → SPred σs) :
  P ∧ (∃ a, Φ a ∨ Ψ a) ⊢ₛ ∃ a, (P ∧ Φ a) ∨ (P ∧ Ψ a) := by
  mintro ⟨HP, ⟨a, ⟨HΦ | HΨ⟩⟩⟩
  · mexists a
    mleft
    mrefine ⟨HP, HΦ⟩
  · mexists a
    mright
    mrefine ⟨HP, HΨ⟩

theorem mosel3 {α : Type} (P : SPred σs) (Φ Ψ : α → SPred σs) :
  P ∧ (∃ a, Φ a ∨ Ψ a) ⊢ₛ ∃ a, Φ a ∨ (P ∧ P ∧ Ψ a) := by
  mintro ⟨HP, ⟨a, ⟨HΦ | HΨ⟩⟩⟩
  · mexists a
    mleft
    mexact HΦ
  · mexists a
    mright
    mrefine ⟨HP, HP, HΨ⟩
