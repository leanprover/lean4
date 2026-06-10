/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Gladshtein, Sebastian Graf
-/
module

prelude
public import Init.ByCases
public import Std.Internal.Do.Order.Basic
public import Std.Internal.Do.Order.Frame
import Init.Classical
import Init.TacticsExtra

@[expose] public section

set_option linter.missingDocs true
set_option linter.unusedSectionVars false

/-!
# Derived laws of `CompleteLattice`

This module contains some laws about `CompleteLattice` that are derived from
the laws in `Std.Internal.Do.CompleteLattice.CompleteLattice`.
-/


namespace Std.Internal.Do.CompleteLattice

open Lean.Order PartialOrder

universe u v

variable {l : Type u} [CompleteLattice l] {P P' Q Q' R R' T : l} {φ φ₁ φ₂ : Prop}

/-! # Connectives -/

theorem and_intro_l (h : P ⊑ Q) : P ⊑ Q ⊓ P := le_meet _ _ _ h rel_refl
theorem and_intro_r (h : P ⊑ Q) : P ⊑ P ⊓ Q := le_meet _ _ _ rel_refl h
theorem and_intro_eq (hand : T = Q ⊓ R) (hQ : P ⊑ Q) (hR : P ⊑ R) : P ⊑ T := by
  rw [hand]
  exact le_meet _ _ _ hQ hR
theorem and_elim_l' (h : P ⊑ R) : P ⊓ Q ⊑ R := rel_trans (meet_le_left _ _) h
theorem and_elim_r' (h : Q ⊑ R) : P ⊓ Q ⊑ R := rel_trans (meet_le_right _ _) h
theorem or_intro_l' (h : P ⊑ Q) : P ⊑ Q ⊔ R := rel_trans h (left_le_join _ _)
theorem or_intro_r' (h : P ⊑ R) : P ⊑ Q ⊔ R := rel_trans h (right_le_join _ _)
theorem and_symm : P ⊓ Q ⊑ Q ⊓ P := le_meet _ _ _ (meet_le_right _ _) (meet_le_left _ _)
theorem or_symm : P ⊔ Q ⊑ Q ⊔ P := join_le _ _ _ (right_le_join _ _) (left_le_join _ _)
theorem rel_trans' (h₁ : P ⊑ Q) (h₂ : P ⊓ Q ⊑ R) : P ⊑ R := rel_trans (le_meet _ _ _ rel_refl h₁) h₂
theorem false_elim : (⊥ : l) ⊑ P := bot_le _
theorem true_intro : P ⊑ (⊤ : l) := le_top _
theorem exists_intro' {α} {Ψ : α → l} (a : α) (h : P ⊑ Ψ a) : P ⊑ iSup Ψ :=
  rel_trans h (le_iSup _ a)
theorem exfalso (h : P ⊑ (⊥ : l)) : P ⊑ Q := rel_trans h false_elim

/-! ## Connectives requiring `Frame` -/

section Frame
variable [Frame l]

theorem imp_intro (h : P ⊓ Q ⊑ R) : P ⊑ Q ⇨ R := himp_complete _ _ _ (rel_trans and_symm h)
theorem imp_intro' (h : Q ⊓ P ⊑ R) : P ⊑ Q ⇨ R := himp_complete _ _ _ h
theorem imp_elim (h : P ⊑ Q ⇨ R) : P ⊓ Q ⊑ R := rel_trans
  (le_meet _ _ _ (meet_le_right _ _) (and_elim_l' h))
  (himp_sound _ _)
theorem imp_elim' (h : Q ⊑ P ⇨ R) : P ⊓ Q ⊑ R := rel_trans and_symm (imp_elim h)
theorem imp_elim_l : (P ⇨ Q) ⊓ P ⊑ Q := imp_elim rel_refl
theorem imp_elim_r : P ⊓ (P ⇨ Q) ⊑ Q := imp_elim' rel_refl
theorem mp (h₁ : P ⊑ Q ⇨ R) (h₂ : P ⊑ Q) : P ⊑ R := rel_trans' h₂ (imp_elim h₁)

theorem and_or_elim_l (hleft : P ⊓ R ⊑ T) (hright : Q ⊓ R ⊑ T) : (P ⊔ Q) ⊓ R ⊑ T :=
  imp_elim (join_le _ _ _ (imp_intro hleft) (imp_intro hright))
theorem and_or_elim_r (hleft : P ⊓ Q ⊑ T) (hright : P ⊓ R ⊑ T) : P ⊓ (Q ⊔ R) ⊑ T :=
  imp_elim'
    (join_le _ _ _
      (imp_intro (rel_trans and_symm hleft))
      (imp_intro (rel_trans and_symm hright)))

end Frame

/-! # Monotonicity -/

theorem and_mono (hp : P ⊑ P') (hq : Q ⊑ Q') : P ⊓ Q ⊑ P' ⊓ Q' :=
  le_meet _ _ _ (and_elim_l' hp) (and_elim_r' hq)
theorem and_mono_l (h : P ⊑ P') : P ⊓ Q ⊑ P' ⊓ Q := and_mono h rel_refl
theorem and_mono_r (h : Q ⊑ Q') : P ⊓ Q ⊑ P ⊓ Q' := and_mono rel_refl h

theorem or_mono (hp : P ⊑ P') (hq : Q ⊑ Q') : P ⊔ Q ⊑ P' ⊔ Q' :=
  join_le _ _ _ (or_intro_l' hp) (or_intro_r' hq)
theorem or_mono_l (h : P ⊑ P') : P ⊔ Q ⊑ P' ⊔ Q := or_mono h rel_refl
theorem or_mono_r (h : Q ⊑ Q') : P ⊔ Q ⊑ P ⊔ Q' := or_mono rel_refl h

theorem forall_mono {α} {Φ Ψ : α → l} (h : ∀ a, Φ a ⊑ Ψ a) : iInf Φ ⊑ iInf Ψ :=
  le_iInf _ _ fun a => rel_trans (iInf_le _ a) (h a)
theorem exists_mono {α} {Φ Ψ : α → l} (h : ∀ a, Φ a ⊑ Ψ a) : iSup Φ ⊑ iSup Ψ :=
  iSup_le _ _ fun a => rel_trans (h a) (le_iSup _ a)

section Frame
variable [Frame l]

theorem imp_mono (h1 : Q ⊑ P) (h2 : P' ⊑ Q') : (P ⇨ P') ⊑ Q ⇨ Q' :=
  imp_intro <| rel_trans (and_mono_r h1) <| rel_trans imp_elim_l h2
theorem imp_mono_l (h : P' ⊑ P) : (P ⇨ Q) ⊑ (P' ⇨ Q) := imp_mono h rel_refl
theorem imp_mono_r (h : Q ⊑ Q') : (P ⇨ Q) ⊑ (P ⇨ Q') := imp_mono rel_refl h

end Frame

/-! # Boolean algebra -/

theorem and_self : P ⊓ P = P :=
  rel_antisymm (meet_le_left _ _) (le_meet _ _ _ rel_refl rel_refl)
theorem or_self : P ⊔ P = P :=
  rel_antisymm (join_le _ _ _ rel_refl rel_refl) (left_le_join _ _)
theorem and_comm : P ⊓ Q = Q ⊓ P := rel_antisymm and_symm and_symm
theorem or_comm : P ⊔ Q = Q ⊔ P := rel_antisymm or_symm or_symm
theorem and_assoc : (P ⊓ Q) ⊓ R = P ⊓ (Q ⊓ R) :=
  rel_antisymm
    (le_meet _ _ _ (and_elim_l' (meet_le_left _ _))
      (le_meet _ _ _ (and_elim_l' (meet_le_right _ _)) (meet_le_right _ _)))
    (le_meet _ _ _
      (le_meet _ _ _ (meet_le_left _ _) (and_elim_r' (meet_le_left _ _)))
      (and_elim_r' (meet_le_right _ _)))
theorem or_assoc : (P ⊔ Q) ⊔ R = P ⊔ (Q ⊔ R) :=
  rel_antisymm
    (join_le _ _ _
      (join_le _ _ _ (left_le_join _ _) (or_intro_r' (left_le_join _ _)))
      (or_intro_r' (right_le_join _ _)))
    (join_le _ _ _ (or_intro_l' (left_le_join _ _))
      (join_le _ _ _ (or_intro_l' (right_le_join _ _)) (right_le_join _ _)))

theorem and_eq_right : (P ⊑ Q) ↔ Q ⊓ P = P :=
  ⟨fun h => rel_antisymm (meet_le_right _ _) (le_meet _ _ _ h rel_refl),
   fun h => h ▸ meet_le_left _ _⟩
theorem and_eq_left : (P ⊑ Q) ↔ P ⊓ Q = P :=
  ⟨fun h => rel_antisymm (meet_le_left _ _) (le_meet _ _ _ rel_refl h),
   fun h => h ▸ meet_le_right _ _⟩
theorem or_eq_left : (P ⊑ Q) ↔ Q ⊔ P = Q :=
  ⟨fun h => rel_antisymm (join_le _ _ _ rel_refl h) (left_le_join _ _),
   fun h => h ▸ right_le_join _ _⟩
theorem or_eq_right : (P ⊑ Q) ↔ P ⊔ Q = Q :=
  ⟨fun h => rel_antisymm (join_le _ _ _ h rel_refl) (right_le_join _ _),
   fun h => h ▸ left_le_join _ _⟩

theorem true_and : (⊤ : l) ⊓ P = P :=
  rel_antisymm (meet_le_right _ _) (le_meet _ _ _ (le_top _) rel_refl)
theorem and_true : P ⊓ (⊤ : l) = P := and_comm.trans true_and
theorem false_and : (⊥ : l) ⊓ P = ⊥ :=
  rel_antisymm (and_elim_l' false_elim) false_elim
theorem and_false : P ⊓ (⊥ : l) = ⊥ := and_comm.trans false_and
theorem true_or : (⊤ : l) ⊔ P = ⊤ :=
  rel_antisymm (le_top _) (left_le_join _ _)
theorem or_true : P ⊔ (⊤ : l) = ⊤ := or_comm.trans true_or
theorem false_or : (⊥ : l) ⊔ P = P :=
  rel_antisymm (join_le _ _ _ false_elim rel_refl) (right_le_join _ _)
theorem or_false : P ⊔ (⊥ : l) = P := or_comm.trans false_or

section Frame
variable [Frame l]

theorem and_or_left : P ⊓ (Q ⊔ R) = (P ⊓ Q) ⊔ (P ⊓ R) :=
  rel_antisymm
    (and_or_elim_r (or_intro_l' rel_refl) (or_intro_r' rel_refl))
    (join_le _ _ _ (and_mono_r (left_le_join _ _)) (and_mono_r (right_le_join _ _)))
theorem or_and_left : P ⊔ (Q ⊓ R) = (P ⊔ Q) ⊓ (P ⊔ R) :=
  rel_antisymm
    (join_le _ _ _ (le_meet _ _ _ (left_le_join _ _) (left_le_join _ _))
      (and_mono (right_le_join _ _) (right_le_join _ _)))
    (and_or_elim_l (or_intro_l' (meet_le_left _ _))
      (and_or_elim_r (or_intro_l' (meet_le_right _ _)) (or_intro_r' rel_refl)))
theorem or_and_right : (P ⊔ Q) ⊓ R = (P ⊓ R) ⊔ (Q ⊓ R) :=
  and_comm.trans (and_or_left.trans (rel_antisymm
    (or_mono (P := _) (Q := _) (P' := _) (Q' := _)
      (rel_of_eq and_comm) (rel_of_eq and_comm))
    (or_mono (rel_of_eq and_comm) (rel_of_eq and_comm))))
theorem and_or_right : (P ⊓ Q) ⊔ R = (P ⊔ R) ⊓ (Q ⊔ R) :=
  or_comm.trans (or_and_left.trans (rel_antisymm
    (and_mono (rel_of_eq or_comm) (rel_of_eq or_comm))
    (and_mono (rel_of_eq or_comm) (rel_of_eq or_comm))))

theorem true_imp : ((⊤ : l) ⇨ P) = P :=
  rel_antisymm
    (rel_trans (le_meet _ _ _ (le_top _) rel_refl) imp_elim_r)
    (imp_intro (and_elim_l' rel_refl))
theorem imp_self : Q ⊑ P ⇨ P := imp_intro (meet_le_right _ _)
theorem imp_self_simp : (Q ⊑ P ⇨ P) ↔ True := iff_true_intro imp_self
theorem imp_trans : (P ⇨ Q) ⊓ (Q ⇨ R) ⊑ P ⇨ R :=
  imp_intro' <|
    rel_trans (rel_of_eq and_assoc.symm) <|
      rel_trans (and_mono_l imp_elim_r) imp_elim_r
theorem false_imp : ((⊥ : l) ⇨ P) = ⊤ :=
  rel_antisymm (le_top _) (imp_intro (and_elim_r' false_elim))

theorem and_imp : P' ⊓ (P' ⇨ Q') ⊑ P' ⊓ Q' :=
  le_meet _ _ _ (meet_le_left _ _) (rel_trans and_symm imp_elim_l)
theorem of_and_imp (hp : P ⊑ P') (hq : Q ⊑ (P' ⇨ Q')) : P ⊓ Q ⊑ P' ⊓ Q' :=
  rel_trans (and_mono hp hq) and_imp

end Frame

/-! # Pure (`CompleteLattice.ofProp`) -/

theorem pure_elim {φ : Prop} (h1 : Q ⊑ (⌜φ⌝ : l)) (h2 : φ → Q ⊑ R) : Q ⊑ R := by
  by_cases hφ : φ
  · exact h2 hφ
  · simp [CompleteLattice.ofProp, hφ] at h1
    exact rel_trans h1 false_elim

theorem pure_mono {φ₁ φ₂ : Prop} (h : φ₁ → φ₂) : ⌜φ₁⌝ ⊑ (⌜φ₂⌝ : l) :=
  CompleteLattice.ofProp_imp _ _ h
theorem pure_congr {φ₁ φ₂ : Prop} (h : φ₁ ↔ φ₂) : (⌜φ₁⌝ : l) = ⌜φ₂⌝ :=
  rel_antisymm (pure_mono h.1) (pure_mono h.2)

theorem pure_elim_l {φ : Prop} (h : φ → Q ⊑ R) : (⌜φ⌝ : l) ⊓ Q ⊑ R := by
  rw [CompleteLattice.ofProp_intro_r]; exact h
theorem pure_elim_r {φ : Prop} (h : φ → Q ⊑ R) : Q ⊓ (⌜φ⌝ : l) ⊑ R := by
  rw [CompleteLattice.ofProp_intro_l]; exact h
theorem pure_true {φ : Prop} (h : φ) : (⌜φ⌝ : l) = ⌜True⌝ := pure_congr ⟨fun _ => trivial, fun _ => h⟩

theorem pure_and {φ₁ φ₂ : Prop} : (⌜φ₁⌝ : l) ⊓ ⌜φ₂⌝ = ⌜φ₁ ∧ φ₂⌝ := by
  apply rel_antisymm
  · apply pure_elim_r
    intro h₂
    apply pure_mono
    exact (⟨·, h₂⟩)
  · exact le_meet _ _ _ (pure_mono And.left) (pure_mono And.right)

theorem pure_or {φ₁ φ₂ : Prop} : (⌜φ₁⌝ : l) ⊔ ⌜φ₂⌝ = ⌜φ₁ ∨ φ₂⌝ := by
  apply rel_antisymm
  · exact join_le _ _ _ (pure_mono Or.inl) (pure_mono Or.inr)
  · rw [CompleteLattice.ofProp_intro]
    rintro (h₁ | h₂)
    · rw [pure_true h₁, CompleteLattice.ofProp_true]
      exact left_le_join _ _
    · rw [pure_true h₂, CompleteLattice.ofProp_true]
      exact right_le_join _ _

theorem pure_forall_2 {α} {Φ : α → Prop} : (⌜∀ x, Φ x⌝ : l) ⊑ iInf (fun x => ⌜Φ x⌝) :=
  le_iInf _ _ fun _ => pure_mono (· _)

theorem pure_exists {α} {Φ : α → Prop} :
    iSup (fun x => (⌜Φ x⌝ : l)) = ⌜∃ x, Φ x⌝ := by
  apply rel_antisymm
  · exact iSup_le _ _ fun a => pure_mono (⟨a, ·⟩)
  · rw [CompleteLattice.ofProp_intro]
    rintro ⟨x, hx⟩
    have h : (⌜Φ x⌝ : l) = ⊤ := by rw [pure_true hx, CompleteLattice.ofProp_true]
    exact h ▸ le_iSup (fun x => (⌜Φ x⌝ : l)) x

theorem pure_forall {α} {Φ : α → Prop} :
    iInf (fun x => (⌜Φ x⌝ : l)) = ⌜∀ x, Φ x⌝ := by
  apply rel_antisymm
  · by_cases h : ∃ x, ¬Φ x
    · obtain ⟨x, hx⟩ := h
      exact rel_trans (iInf_le _ x) (pure_mono hx.elim)
    · have hall : ∀ x, Φ x := fun x => Classical.not_not.1 <| mt (⟨x, ·⟩) h
      have heq : (⌜∀ x, Φ x⌝ : l) = ⊤ := by rw [pure_true hall, CompleteLattice.ofProp_true]
      exact heq ▸ le_top _
  · exact pure_forall_2

section Frame
variable [Frame l]

theorem pure_imp_2 {φ₁ φ₂ : Prop} : (⌜φ₁ → φ₂⌝ : l) ⊑ (⌜φ₁⌝ ⇨ ⌜φ₂⌝) :=
  imp_intro (rel_trans (rel_of_eq pure_and) (pure_mono (And.elim id)))

theorem pure_imp {φ₁ φ₂ : Prop} : ((⌜φ₁⌝ : l) ⇨ ⌜φ₂⌝) = ⌜φ₁ → φ₂⌝ := by
  apply rel_antisymm
  · by_cases h₁ : φ₁
    · -- φ₁ true: goal `(⌜φ₁⌝ ⇨ ⌜φ₂⌝) ⊑ ⌜φ₁ → φ₂⌝`. Use `imp_elim_l` after weakening LHS to `⌜φ₁⌝ ⇨ ⌜φ₂⌝ ⊓ ⌜φ₁⌝`.
      have h₁' : (⊤ : l) ⊑ ⌜φ₁⌝ := by
        have : (⌜φ₁⌝ : l) = ⊤ := by rw [pure_true h₁, CompleteLattice.ofProp_true]
        exact this ▸ rel_refl
      exact rel_trans
        (le_meet _ _ _ rel_refl (rel_trans (le_top _) h₁'))
        (rel_trans imp_elim_l (pure_mono (fun h _ => h)))
    · -- φ₁ false: ⌜φ₁⌝ = ⊥, ⌜φ₁ → φ₂⌝ = ⊤
      have : (⌜φ₁ → φ₂⌝ : l) = ⊤ := by rw [pure_true (fun hp => absurd hp h₁), CompleteLattice.ofProp_true]
      exact this ▸ le_top _
  · exact pure_imp_2

end Frame

/-! # Miscellaneous -/

theorem and_left_comm : P ⊓ (Q ⊓ R) = Q ⊓ (P ⊓ R) := by
  rw [← and_assoc, and_comm (P := P), and_assoc]
theorem and_right_comm : (P ⊓ Q) ⊓ R = (P ⊓ R) ⊓ Q := by
  rw [and_assoc, and_comm (P := Q), ← and_assoc]

/-! # Working with entailment -/

/-- `⊤ ⊑ (P ⇨ Q)` iff `P ⊑ Q`. Analogue of `entails_true_intro` for SPred. -/
@[simp] theorem top_le_himp_iff [Frame l] (P Q : l) :
    ((⊤ : l) ⊑ P ⇨ Q) ↔ (P ⊑ Q) :=
  ⟨fun h => rel_trans
    (le_meet _ _ _ (le_top _) rel_refl)
    (rel_trans (and_mono_l h) imp_elim_l),
   fun h => imp_intro (and_elim_r' h)⟩

@[simp] theorem true_intro_simp : (Q ⊑ (⊤ : l)) ↔ True := iff_true_intro true_intro

/-! ## Pointwise unfoldings of `⊑` on function lattices

Analogues of `Std.Do.SPred.entails_1`–`entails_5` for nested function-space
CompleteLattices. Each is definitional via the function-space `PartialOrder` instance. -/

@[simp] theorem entails_1 {σ : Type v} {P Q : σ → l} :
    P ⊑ Q ↔ ∀ s, P s ⊑ Q s := Iff.rfl
@[simp] theorem entails_2 {σ₁ σ₂ : Type v} {P Q : σ₁ → σ₂ → l} :
    P ⊑ Q ↔ ∀ s₁ s₂, P s₁ s₂ ⊑ Q s₁ s₂ := Iff.rfl
@[simp] theorem entails_3 {σ₁ σ₂ σ₃ : Type v} {P Q : σ₁ → σ₂ → σ₃ → l} :
    P ⊑ Q ↔ ∀ s₁ s₂ s₃, P s₁ s₂ s₃ ⊑ Q s₁ s₂ s₃ := Iff.rfl
@[simp] theorem entails_4 {σ₁ σ₂ σ₃ σ₄ : Type v} {P Q : σ₁ → σ₂ → σ₃ → σ₄ → l} :
    P ⊑ Q ↔ ∀ s₁ s₂ s₃ s₄, P s₁ s₂ s₃ s₄ ⊑ Q s₁ s₂ s₃ s₄ := Iff.rfl
@[simp] theorem entails_5 {σ₁ σ₂ σ₃ σ₄ σ₅ : Type v} {P Q : σ₁ → σ₂ → σ₃ → σ₄ → σ₅ → l} :
    P ⊑ Q ↔ ∀ s₁ s₂ s₃ s₄ s₅, P s₁ s₂ s₃ s₄ s₅ ⊑ Q s₁ s₂ s₃ s₄ s₅ := Iff.rfl

/-! ## Function-space pointwise lemmas -/

/-- Pointwise version of `pure_and`: meet of pointwise-pure functions is pointwise-pure of `∧`. -/
theorem and_pure_fun {σ : Type v} {β : Type u} [CompleteLattice β] (P P' : σ → Prop) :
    (fun t => (⌜P t⌝ : β)) ⊓ (fun t => (⌜P' t⌝ : β)) = fun t => (⌜P t ∧ P' t⌝ : β) := by
  funext t
  rw [meet_fun_apply, pure_and]

/-! # Tactic support -/

namespace Tactic

/-- A tautology in `CompleteLattice l` (lattice element entailed by `⊤`). -/
abbrev tautological (Q : l) : Prop := (⊤ : l) ⊑ Q

/--
A mapping from propositions to `CompleteLattice`-level tautologies that are known to be logically
equivalent. This is used to rewrite proof goals into a form that is suitable for use with
`mvcgen`.
-/
class PropAsCompleteLatticeTautology (φ : Prop) {l : outParam (Type u)} [outParam (CompleteLattice l)]
    (P : outParam l) : Prop where
  /-- A proof that `φ` and `P` are logically equivalent. -/
  iff : φ ↔ ((⊤ : l) ⊑ P)

instance [Frame l] (P Q : l) : PropAsCompleteLatticeTautology (P ⊑ Q) (P ⇨ Q) where
  iff := (top_le_himp_iff P Q).symm

instance (P : l) : PropAsCompleteLatticeTautology ((⊤ : l) ⊑ P) P where iff := Iff.rfl

/--
A mapping from `CompleteLattice` elements to pure propositions that are known to be equivalent.
-/
class IsPure (P : l) (φ : outParam Prop) where
  /-- A proof that `P` and `⌜φ⌝` are equal. -/
  to_pure : P = ⌜φ⌝

instance (φ : Prop) : IsPure (⌜φ⌝ : l) φ where to_pure := rfl
instance : IsPure (l := l) ⊤ True where to_pure := (CompleteLattice.ofProp_true l).symm
instance : IsPure (l := l) ⊥ False where to_pure := (CompleteLattice.ofProp_false l).symm
instance (φ ψ : Prop) : IsPure (l := l) (⌜φ⌝ ⊓ ⌜ψ⌝) (φ ∧ ψ) where to_pure := pure_and
instance (φ ψ : Prop) : IsPure (l := l) (⌜φ⌝ ⊔ ⌜ψ⌝) (φ ∨ ψ) where to_pure := pure_or
instance [Frame l] (φ ψ : Prop) : IsPure (l := l) (⌜φ⌝ ⇨ ⌜ψ⌝) (φ → ψ) where to_pure := pure_imp
instance {α} (P : α → Prop) :
    IsPure (l := l) (iSup (⌜P ·⌝)) (∃ x, P x) where to_pure := pure_exists
instance {α} (P : α → Prop) :
    IsPure (l := l) (iInf (⌜P ·⌝)) (∀ x, P x) where to_pure := pure_forall
instance {σ : Type u} (s : σ) (P : σ → l) [inst : IsPure P φ] :
    IsPure (l := l) (P s) φ where
  to_pure := (congrFun inst.to_pure s).trans (CompleteLattice.ofProp_fun_apply _ _)
instance {σ : Type u} (P : l) [inst : IsPure P φ] :
    IsPure (l := σ → l) (fun _ => P) φ where
  to_pure := funext fun _ => inst.to_pure.trans (CompleteLattice.ofProp_fun_apply _ _).symm
/--
A decomposition of an CompleteLattice into the meet of two other CompleteLattices.

Decomposing CompleteLattices in postconditions into meets of simpler predicates increases the
chance that automation will be able to prove the entailment of the postcondition and the next
precondition.
-/
class IsAnd (P : l) (Q₁ Q₂ : outParam l) where
  /-- A proof that the decomposition is logically equivalent to the original predicate. -/
  to_and : P = Q₁ ⊓ Q₂

instance (Q₁ Q₂ : l) : IsAnd (Q₁ ⊓ Q₂) Q₁ Q₂ where to_and := rfl
instance (priority := high) [inst : IsAnd P P' Q] (R : l) : IsAnd (P ⊓ R) P' (Q ⊓ R) where
  to_and := by rw [inst.to_and, and_assoc]
instance (p q : Prop) : IsAnd (l := l) ⌜p ∧ q⌝ ⌜p⌝ ⌜q⌝ where to_and := pure_and.symm

theorem ProofMode.start_entails {P : l} {φ : Prop} [PropAsCompleteLatticeTautology φ P] :
    (⊤ ⊑ P) → φ := PropAsCompleteLatticeTautology.iff.mpr
theorem ProofMode.elim_entails {P : l} {φ : Prop} [PropAsCompleteLatticeTautology φ P] :
    φ → (⊤ ⊑ P) := PropAsCompleteLatticeTautology.iff.mp

theorem Assumption.left {P Q R : l} (h : P ⊑ R) : P ⊓ Q ⊑ R := and_elim_l' h
theorem Assumption.right {P Q R : l} (h : Q ⊑ R) : P ⊓ Q ⊑ R := and_elim_r' h

theorem Cases.add_goal {P Q H T : l} (hand : Q ⊓ H = P) (hgoal : P ⊑ T) : Q ⊓ H ⊑ T :=
  hand ▸ hgoal
theorem Cases.clear {Q H T : l} (hgoal : Q ⊓ ⊤ ⊑ T) : Q ⊓ H ⊑ T :=
  rel_trans (and_mono_r (le_top _)) hgoal
theorem Cases.pure {Q T : l} (hgoal : Q ⊓ ⊤ ⊑ T) : Q ⊑ T :=
  rel_trans (le_meet _ _ _ rel_refl (le_top _)) hgoal
theorem Cases.and_1 {Q H₁' H₂' H₁₂' T : l} (hand : H₁' ⊓ H₂' = H₁₂')
    (hgoal : Q ⊓ H₁₂' ⊑ T) : (Q ⊓ H₁') ⊓ H₂' ⊑ T := by
  rw [and_assoc, hand]; exact hgoal
theorem Cases.and_2 {Q H₁' H₂ T : l} (hgoal : (Q ⊓ H₁') ⊓ H₂ ⊑ T) :
    (Q ⊓ H₂) ⊓ H₁' ⊑ T := by
  rw [and_right_comm]; exact hgoal
theorem Cases.and_3 {Q H₁ H₂ H T : l} (hand : H = H₁ ⊓ H₂)
    (hgoal : (Q ⊓ H₂) ⊓ H₁ ⊑ T) : Q ⊓ H ⊑ T := by
  rw [hand, ← and_assoc, and_right_comm]; exact hgoal
theorem Cases.exists [Frame l] {Q : l} {α} {ψ : α → l} {T : l}
    (h : ∀ a, Q ⊓ ψ a ⊑ T) : Q ⊓ iSup ψ ⊑ T :=
  imp_elim' (iSup_le _ _ fun a => imp_intro (rel_trans and_symm (h a)))

theorem Clear.clear {P P' A Q : l} (hfocus : P = P' ⊓ A) (h : P' ⊑ Q) : P ⊑ Q :=
  hfocus ▸ rel_trans (meet_le_left _ _) h
theorem Exact.assumption {P P' A : l} (h : P = P' ⊓ A) : P ⊑ A :=
  h ▸ meet_le_right _ _
theorem Exact.from_tautology {P T : l} {φ : Prop}
    [PropAsCompleteLatticeTautology φ T] (h : φ) : P ⊑ T :=
  rel_trans (le_top _) (PropAsCompleteLatticeTautology.iff.mp h)

theorem Focus.this {P : l} : P = ⊤ ⊓ P := true_and.symm
theorem Focus.left {P P' Q C R : l} (h₁ : P = P' ⊓ R) (h₂ : P' ⊓ Q = C) :
    P ⊓ Q = C ⊓ R := by rw [h₁, and_right_comm, h₂]
theorem Focus.right {P Q Q' C R : l} (h₁ : Q = Q' ⊓ R) (h₂ : P ⊓ Q' = C) :
    P ⊓ Q = C ⊓ R := by rw [h₁, ← and_assoc, h₂]
theorem Focus.rewrite_hyps {P Q R : l} (hrw : P = Q) (hgoal : Q ⊑ R) : P ⊑ R := hrw ▸ hgoal

theorem Have.dup {P Q H T : l} (hfoc : P = Q ⊓ H) (hgoal : P ⊓ H ⊑ T) : P ⊑ T :=
  rel_trans (le_meet _ _ _ rel_refl (hfoc ▸ meet_le_right _ _)) hgoal
theorem Have.have {P H PH T : l} (hand : P ⊓ H = PH) (hhave : P ⊑ H) (hgoal : PH ⊑ T) : P ⊑ T :=
  rel_trans (le_meet _ _ _ rel_refl hhave) (hand ▸ hgoal)
theorem Have.replace {P H H' PH PH' T : l} (hfoc : PH = P ⊓ H) (hand : P ⊓ H' = PH')
    (hhave : PH ⊑ H') (hgoal : PH' ⊑ T) : PH ⊑ T :=
  rel_trans
    (le_meet _ _ _ (hfoc ▸ meet_le_left _ _) hhave) (hand ▸ hgoal)

theorem Intro.intro [Frame l] {P Q H T : l} (hand : Q ⊓ H = P) (h : P ⊑ T) : Q ⊑ H ⇨ T :=
  imp_intro (hand ▸ h)
theorem Revert.and_pure_intro_r {φ : Prop} {P P' Q : l}
    (h₁ : φ) (hand : P ⊓ ⌜φ⌝ = P') (h₂ : P' ⊑ Q) : P ⊑ Q := by
  rw [pure_true h₁, CompleteLattice.ofProp_true (l := l)] at hand
  exact rel_trans
    (le_meet _ _ _ rel_refl (le_top _)) (hand ▸ h₂)
theorem Pure.thm {P Q T : l} {φ : Prop} [IsPure Q φ] (h : φ → P ⊑ T) : P ⊓ Q ⊑ T := by
  rw [IsPure.to_pure (P := Q)]
  exact pure_elim_r h
/-- A generalization of `pure_intro` exploiting `IsPure`. -/
theorem Pure.intro {P Q : l} {φ : Prop} [IsPure Q φ] (hφ : φ) : P ⊑ Q := by
  rw [IsPure.to_pure (P := Q), pure_true hφ, CompleteLattice.ofProp_true]
  exact le_top _
theorem Revert.revert [Frame l] {P Q H T : l} (hfoc : P = Q ⊓ H) (h : Q ⊑ H ⇨ T) : P ⊑ T :=
  hfoc ▸ imp_elim h

theorem Specialize.imp_stateful [Frame l] {P P' Q R : l}
    (hrefocus : P ⊓ (Q ⇨ R) = P' ⊓ Q) : P ⊓ (Q ⇨ R) ⊑ P ⊓ R := by
  refine rel_trans
    (le_meet _ _ _ (rel_of_eq hrefocus) (meet_le_right _ _)) ?_
  rw [and_assoc]
  refine rel_trans (and_mono_r (le_meet _ _ _ (meet_le_left _ _) imp_elim_r)) ?_
  rw [← and_assoc]
  exact and_mono_l (rel_trans (rel_of_eq hrefocus.symm) (meet_le_left _ _))

theorem Specialize.imp_pure [Frame l] {P Q R : l} {φ : Prop}
    [PropAsCompleteLatticeTautology φ Q] (h : φ) : P ⊓ (Q ⇨ R) ⊑ P ⊓ R :=
  and_mono_r
    (rel_trans
      (le_meet _ _ _
        (rel_trans (le_top _) (PropAsCompleteLatticeTautology.iff.mp h))
        rel_refl)
      (mp (meet_le_right _ _) (meet_le_left _ _)))

theorem Specialize.forall {α} {ψ : α → l} {P : l} (a : α) :
    P ⊓ iInf ψ ⊑ P ⊓ ψ a := and_mono_r (iInf_le _ a)
theorem Specialize.pure_start {φ : Prop} {H P T : l}
    [PropAsCompleteLatticeTautology φ H] (hpure : φ) (hgoal : P ⊓ H ⊑ T) : P ⊑ T :=
  rel_trans (le_meet _ _ _ rel_refl
    (rel_trans (le_top _) (PropAsCompleteLatticeTautology.iff.mp hpure))) hgoal
theorem Specialize.pure_taut {φ} {P : l} [IsPure P φ] (h : φ) : (⊤ : l) ⊑ P := by
  rw [IsPure.to_pure (P := P), pure_true h, CompleteLattice.ofProp_true]
theorem Specialize.focus {P P' Q R : l} (hfocus : P = P' ⊓ Q) (hnew : P' ⊓ Q ⊑ R) : P ⊑ R :=
  hfocus ▸ hnew

/-- Expresses that the meet of `P` and `Q` is equal to `P ⊓ Q`, but potentially simpler. -/
class SimpAnd (P Q : l) (PQ : outParam l) : Prop where
  /-- A proof that `P ⊓ Q` equals `PQ`. -/
  simp_and : P ⊓ Q = PQ

instance (P Q : l) : SimpAnd P Q (P ⊓ Q) where simp_and := rfl
instance (P : l) : SimpAnd P ⊤ P where simp_and := and_true
instance (P : l) : SimpAnd ⊤ P P where simp_and := true_and

/--
Provides a decomposition of an CompleteLattice (`P`) into pure (`φ`) and "everything else" (`P'`)
components.
-/
class HasFrame (P : l) (P' : outParam l) (φ : outParam Prop) : Prop where
  /-- A proof that the original CompleteLattice is equal to the decomposed form. -/
  reassoc : P = P' ⊓ ⌜φ⌝

instance [HasFrame P Q φ] [SimpAnd Q P' QP] : HasFrame (P ⊓ P') QP φ where
  reassoc := by rw [HasFrame.reassoc (P := P), and_right_comm, SimpAnd.simp_and (P := Q)]
instance [HasFrame P' Q' φ] [SimpAnd P Q' PQ] : HasFrame (P ⊓ P') PQ φ where
  reassoc := by rw [HasFrame.reassoc (P := P'), ← and_assoc, SimpAnd.simp_and (P := P) (Q := Q')]
instance [HasFrame (⌜p⌝ ⊓ ⌜p'⌝) Q φ] : HasFrame (l := l) ⌜p ∧ p'⌝ Q φ where
  reassoc := pure_and.symm.trans HasFrame.reassoc
instance {σ : Type v} [CompleteLattice β] (P P' : σ → Prop) (Q : σ → β)
  [HasFrame ((⌜P ·⌝) ⊓ (⌜P' ·⌝)) Q φ] : HasFrame (fun t => ⌜P t ∧ P' t⌝) Q φ where
  reassoc := (and_pure_fun P P').symm.trans HasFrame.reassoc
instance (P : l) : HasFrame (l := l) (⌜φ⌝ ⊓ P) P φ where reassoc := and_comm
instance (P : l) : HasFrame (l := l) (P ⊓ ⌜φ⌝) P φ where reassoc := rfl
instance [HasFrame P Q φ] [HasFrame P' Q' ψ] [SimpAnd Q Q' QQ] : HasFrame (P ⊓ P') QQ (φ ∧ ψ) where
  reassoc := by
    rw [HasFrame.reassoc (P := P), HasFrame.reassoc (P := P'),
        and_assoc, and_left_comm (P := (⌜φ⌝ : l)), ← and_assoc,
        pure_and, SimpAnd.simp_and (P := Q)]
instance [HasFrame P Q ψ] : HasFrame (l := l) (⌜φ⌝ ⊓ P) Q (φ ∧ ψ) where
  reassoc := by rw [HasFrame.reassoc (P := P), and_left_comm, pure_and]
instance [HasFrame P Q ψ] : HasFrame (l := l) (P ⊓ ⌜φ⌝) Q (ψ ∧ φ) where
  reassoc := by rw [HasFrame.reassoc (P := P), and_assoc, pure_and]
-- The following instance comes last so that it gets the highest priority.
-- It's the most efficient and best solution if valid
instance (φ : Prop) : HasFrame (l := l) ⌜φ⌝ ⊤ φ where reassoc := true_and.symm

theorem Frame.frame {P Q T : l} {φ : Prop} [HasFrame P Q φ]
    (h : φ → Q ⊑ T) : P ⊑ T := by
  rw [HasFrame.reassoc (P := P)]
  exact pure_elim_r h

end Tactic

end Std.Internal.Do.CompleteLattice
