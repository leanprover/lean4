/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Sebastian Graf
-/
module

prelude
public import Std.Do.SPred.Notation

@[expose] public section

set_option linter.missingDocs true

namespace Std.Do.SPred

/-!
# Laws of `SPred`

This module contains lemmas about `SPred` that need to be proved by induction on σs.
That is, they need to proved by appealing to the model of `SPred` and cannot
be derived without doing so.

`Std.Do.SPred.DerivedLaws` has some more laws that are derivative of what follows.
-/

universe u
variable {σs : List (Type u)}

/-! # Entailment -/

@[refl, simp, grind ←]
theorem entails.refl (P : SPred σs) : P ⊢ₛ P := by
  induction σs with
  | nil => simp [entails]
  | cons σ _ ih => intro s; exact ih (P s)

theorem entails.trans {P Q R : SPred σs} : (P ⊢ₛ Q) → (Q ⊢ₛ R) → (P ⊢ₛ R) := by
  induction σs with
  | nil => intro h₁ h₂; exact h₂ ∘ h₁
  | cons σ _ ih => intro h₁ h₂; intro s; exact ih (h₁ s) (h₂ s)

instance : Trans (@entails σs) entails entails where
  trans := entails.trans

/-! # Bientailment -/

theorem bientails.iff {P Q : SPred σs} : P ⊣⊢ₛ Q ↔ (P ⊢ₛ Q) ∧ (Q ⊢ₛ P) := by
  induction σs with
  | nil => exact Iff.intro (fun h => ⟨h.mp, h.mpr⟩) (fun h => ⟨h.1, h.2⟩)
  | cons σ σs ih
  apply Iff.intro
  · exact fun h => ⟨fun s => (ih.mp (h s)).1, fun s => (ih.mp (h s)).2⟩
  · intro h s; exact ih.mpr ⟨h.1 s, h.2 s⟩

@[refl, simp]
theorem bientails.refl (P : SPred σs) : P ⊣⊢ₛ P := by
  induction σs <;> simp [bientails, *]

theorem bientails.trans {P Q R : SPred σs} : (P ⊣⊢ₛ Q) → (Q ⊣⊢ₛ R) → (P ⊣⊢ₛ R) := by
  induction σs
  case nil => simp +contextual only [bientails, implies_true]
  case cons σ σs ih => intro hpq hqr s; exact ih (hpq s) (hqr s)

instance : Trans (@bientails σs) bientails bientails where
  trans := bientails.trans

theorem bientails.symm {P Q : SPred σs} : (P ⊣⊢ₛ Q) → (Q ⊣⊢ₛ P) := by
  induction σs
  case nil => exact Iff.symm
  case cons σ σs ih => intro h s; exact ih (h s)

theorem bientails.to_eq {P Q : SPred σs} (h : P ⊣⊢ₛ Q) : P = Q := by
  induction σs
  case nil => ext; rw [iff_iff_eq.mp h]
  case cons σ σs ih =>
    ext s; rw[ih (h s)]

/-! # Pure -/

@[simp, grind =] theorem down_pure {φ : Prop} : (⌜φ⌝ : SPred []).down = φ := rfl
@[simp, grind =] theorem apply_pure {φ : Prop} : (⌜φ⌝ : SPred (σ::σs)) s = ⌜φ⌝ := rfl

theorem pure_intro {φ : Prop} {P : SPred σs} : φ → P ⊢ₛ ⌜φ⌝ := by
  induction σs <;> simp_all [entails]

theorem pure_elim' {φ : Prop} {P : SPred σs} : (φ → ⌜True⌝ ⊢ₛ P) → ⌜φ⌝ ⊢ₛ P := by
  induction σs <;> simp_all [entails]

-- Ideally, we'd like to prove the following theorem:
-- theorem pure_elim' {φ : Prop} : SPred.entails (σs:=σs) ⌜True⌝ ⌜φ⌝ → φ
-- Unfortunately, this is only true if all `σs` are Inhabited.

/-! # Conjunction -/

theorem and_intro {P Q R : SPred σs} (h1 : P ⊢ₛ Q) (h2 : P ⊢ₛ R) : P ⊢ₛ Q ∧ R := by
  induction σs <;> simp_all [entails]

theorem and_elim_l {P Q : SPred σs} : P ∧ Q ⊢ₛ P := by
  induction σs <;> simp_all [entails]

theorem and_elim_r {P Q : SPred σs} : P ∧ Q ⊢ₛ Q := by
  induction σs <;> simp_all [entails]

/-! # Disjunction -/

theorem or_intro_l {P Q : SPred σs} : P ⊢ₛ P ∨ Q := by
  induction σs <;> simp_all [entails]

theorem or_intro_r {P Q : SPred σs} : Q ⊢ₛ P ∨ Q := by
  induction σs <;> simp_all [entails]

theorem or_elim {P Q R : SPred σs} (h1 : P ⊢ₛ R) (h2 : Q ⊢ₛ R) : P ∨ Q ⊢ₛ R := by
  induction σs
  case nil => exact (Or.elim · h1 h2)
  case cons => simp_all [entails]

/-! # Implication -/

theorem imp_intro {P Q R : SPred σs} (h : P ∧ Q ⊢ₛ R) : P ⊢ₛ Q → R := by
  induction σs <;> simp_all [entails]

theorem imp_elim {P Q R : SPred σs} (h : P ⊢ₛ Q → R) : P ∧ Q ⊢ₛ R := by
  induction σs <;> simp_all [entails]

/-! # Quantifiers -/

theorem forall_intro {P : SPred σs} {Ψ : α → SPred σs} (h : ∀ a, P ⊢ₛ Ψ a) : P ⊢ₛ ∀ a, Ψ a := by
  induction σs <;> simp_all [entails]

theorem forall_elim {Ψ : α → SPred σs} (a : α) : (∀ a, Ψ a) ⊢ₛ Ψ a := by
  induction σs <;> simp_all [entails]

theorem exists_intro {Ψ : α → SPred σs} (a : α) : Ψ a ⊢ₛ ∃ a, Ψ a := by
  induction σs
  case nil => intro _; exists a
  case cons σ σs ih => intro s; exact @ih (fun a => Ψ a s)

theorem exists_elim {Φ : α → SPred σs} {Q : SPred σs} (h : ∀ a, Φ a ⊢ₛ Q) : (∃ a, Φ a) ⊢ₛ Q := by
  induction σs
  case nil => intro ⟨a, ha⟩; exact h a ha
  case cons σ σs ih => intro s; exact ih (fun a => h a s)

/-! # Curry -/

theorem and_curry {P Q : SVal.StateTuple σs → Prop} : SVal.curry (fun t => ⟨P t⟩) ∧ SVal.curry (fun t => ⟨Q t⟩) ⊣⊢ₛ (SVal.curry fun t => ⟨P t ∧ Q t⟩) := by
  induction σs
  case nil => rfl
  case cons σ σs ih => intro s; simp only [and_cons, SVal.curry_cons]; exact ih

theorem or_curry {P Q : SVal.StateTuple σs → Prop} : SVal.curry (fun t => ⟨P t⟩) ∨ SVal.curry (fun t => ⟨Q t⟩) ⊣⊢ₛ (SVal.curry fun t => ⟨P t ∨ Q t⟩) := by
  induction σs
  case nil => rfl
  case cons σ σs ih => intro s; simp only [or_cons, SVal.curry_cons]; exact ih

theorem imp_curry {P Q : SVal.StateTuple σs → Prop} : (SVal.curry (fun t => ⟨P t⟩) → SVal.curry (fun t => ⟨Q t⟩)) ⊣⊢ₛ (SVal.curry fun t => ⟨P t → Q t⟩) := by
  induction σs
  case nil => rfl
  case cons σ σs ih => intro s; simp only [imp_cons, SVal.curry_cons]; exact ih
