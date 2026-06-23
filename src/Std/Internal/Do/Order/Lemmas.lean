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

theorem le_meet_left (h : P ⊑ Q) : P ⊑ Q ⊓ P := le_meet _ _ _ h rel_refl
theorem le_meet_right (h : P ⊑ Q) : P ⊑ P ⊓ Q := le_meet _ _ _ rel_refl h
theorem le_meet_of_eq (hand : T = Q ⊓ R) (hQ : P ⊑ Q) (hR : P ⊑ R) : P ⊑ T := by
  rw [hand]
  exact le_meet _ _ _ hQ hR
theorem meet_le_of_left_le (h : P ⊑ R) : P ⊓ Q ⊑ R := rel_trans (meet_le_left _ _) h
theorem meet_le_of_right_le (h : Q ⊑ R) : P ⊓ Q ⊑ R := rel_trans (meet_le_right _ _) h
theorem le_join_of_le_left (h : P ⊑ Q) : P ⊑ Q ⊔ R := rel_trans h (left_le_join _ _)
theorem le_join_of_le_right (h : P ⊑ R) : P ⊑ Q ⊔ R := rel_trans h (right_le_join _ _)
theorem meet_le_comm : P ⊓ Q ⊑ Q ⊓ P := le_meet _ _ _ (meet_le_right _ _) (meet_le_left _ _)
theorem join_le_comm : P ⊔ Q ⊑ Q ⊔ P := join_le _ _ _ (right_le_join _ _) (left_le_join _ _)
theorem le_trans_meet (h₁ : P ⊑ Q) (h₂ : P ⊓ Q ⊑ R) : P ⊑ R := rel_trans (le_meet _ _ _ rel_refl h₁) h₂
theorem le_iSup_of_le {α} {Ψ : α → l} (a : α) (h : P ⊑ Ψ a) : P ⊑ iSup Ψ :=
  rel_trans h (le_iSup _ a)
theorem le_of_le_bot (h : P ⊑ (⊥ : l)) : P ⊑ Q := rel_trans h (bot_le _)

/-! ## Connectives requiring `Frame` -/

section Frame
variable [Frame l]

theorem le_himp (h : P ⊓ Q ⊑ R) : P ⊑ Q ⇨ R := himp_complete _ _ _ (rel_trans meet_le_comm h)
theorem le_himp_of_meet_le_comm (h : Q ⊓ P ⊑ R) : P ⊑ Q ⇨ R := himp_complete _ _ _ h
theorem meet_le_of_le_himp (h : P ⊑ Q ⇨ R) : P ⊓ Q ⊑ R := rel_trans
  (le_meet _ _ _ (meet_le_right _ _) (meet_le_of_left_le h))
  (himp_sound _ _)
theorem meet_le_of_le_himp_comm (h : Q ⊑ P ⇨ R) : P ⊓ Q ⊑ R :=
  rel_trans meet_le_comm (meet_le_of_le_himp h)
theorem himp_meet_le : (P ⇨ Q) ⊓ P ⊑ Q := meet_le_of_le_himp rel_refl
theorem meet_himp_le : P ⊓ (P ⇨ Q) ⊑ Q := meet_le_of_le_himp_comm rel_refl
theorem le_himp_mp (h₁ : P ⊑ Q ⇨ R) (h₂ : P ⊑ Q) : P ⊑ R :=
  le_trans_meet h₂ (meet_le_of_le_himp h₁)

theorem meet_join_le_left (hleft : P ⊓ R ⊑ T) (hright : Q ⊓ R ⊑ T) : (P ⊔ Q) ⊓ R ⊑ T :=
  meet_le_of_le_himp (join_le _ _ _ (le_himp hleft) (le_himp hright))
theorem meet_join_le_right (hleft : P ⊓ Q ⊑ T) (hright : P ⊓ R ⊑ T) : P ⊓ (Q ⊔ R) ⊑ T :=
  meet_le_of_le_himp_comm
    (join_le _ _ _
      (le_himp (rel_trans meet_le_comm hleft))
      (le_himp (rel_trans meet_le_comm hright)))

end Frame

/-! # Monotonicity -/

theorem meet_mono (hp : P ⊑ P') (hq : Q ⊑ Q') : P ⊓ Q ⊑ P' ⊓ Q' :=
  le_meet _ _ _ (meet_le_of_left_le hp) (meet_le_of_right_le hq)
theorem meet_mono_left (h : P ⊑ P') : P ⊓ Q ⊑ P' ⊓ Q := meet_mono h rel_refl
theorem meet_mono_right (h : Q ⊑ Q') : P ⊓ Q ⊑ P ⊓ Q' := meet_mono rel_refl h

theorem join_mono (hp : P ⊑ P') (hq : Q ⊑ Q') : P ⊔ Q ⊑ P' ⊔ Q' :=
  join_le _ _ _ (le_join_of_le_left hp) (le_join_of_le_right hq)
theorem join_mono_left (h : P ⊑ P') : P ⊔ Q ⊑ P' ⊔ Q := join_mono h rel_refl
theorem join_mono_right (h : Q ⊑ Q') : P ⊔ Q ⊑ P ⊔ Q' := join_mono rel_refl h

theorem iInf_mono {α} {Φ Ψ : α → l} (h : ∀ a, Φ a ⊑ Ψ a) : iInf Φ ⊑ iInf Ψ :=
  le_iInf _ _ fun a => rel_trans (iInf_le _ a) (h a)
theorem iSup_mono {α} {Φ Ψ : α → l} (h : ∀ a, Φ a ⊑ Ψ a) : iSup Φ ⊑ iSup Ψ :=
  iSup_le _ _ fun a => rel_trans (h a) (le_iSup _ a)

section Frame
variable [Frame l]

theorem himp_mono (h1 : Q ⊑ P) (h2 : P' ⊑ Q') : (P ⇨ P') ⊑ Q ⇨ Q' :=
  le_himp <| rel_trans (meet_mono_right h1) <| rel_trans himp_meet_le h2
theorem himp_mono_left (h : P' ⊑ P) : (P ⇨ Q) ⊑ (P' ⇨ Q) := himp_mono h rel_refl
theorem himp_mono_right (h : Q ⊑ Q') : (P ⇨ Q) ⊑ (P ⇨ Q') := himp_mono rel_refl h

end Frame

/-! # Boolean algebra -/

theorem meet_self : P ⊓ P = P :=
  rel_antisymm (meet_le_left _ _) (le_meet _ _ _ rel_refl rel_refl)
theorem join_self : P ⊔ P = P :=
  rel_antisymm (join_le _ _ _ rel_refl rel_refl) (left_le_join _ _)
theorem meet_comm : P ⊓ Q = Q ⊓ P := rel_antisymm meet_le_comm meet_le_comm
theorem join_comm : P ⊔ Q = Q ⊔ P := rel_antisymm join_le_comm join_le_comm
theorem meet_assoc : (P ⊓ Q) ⊓ R = P ⊓ (Q ⊓ R) :=
  rel_antisymm
    (le_meet _ _ _ (meet_le_of_left_le (meet_le_left _ _))
      (le_meet _ _ _ (meet_le_of_left_le (meet_le_right _ _)) (meet_le_right _ _)))
    (le_meet _ _ _
      (le_meet _ _ _ (meet_le_left _ _) (meet_le_of_right_le (meet_le_left _ _)))
      (meet_le_of_right_le (meet_le_right _ _)))
theorem join_assoc : (P ⊔ Q) ⊔ R = P ⊔ (Q ⊔ R) :=
  rel_antisymm
    (join_le _ _ _
      (join_le _ _ _ (left_le_join _ _) (le_join_of_le_right (left_le_join _ _)))
      (le_join_of_le_right (right_le_join _ _)))
    (join_le _ _ _ (le_join_of_le_left (left_le_join _ _))
      (join_le _ _ _ (le_join_of_le_left (right_le_join _ _)) (right_le_join _ _)))

theorem le_iff_meet_eq_right : (P ⊑ Q) ↔ Q ⊓ P = P :=
  ⟨fun h => rel_antisymm (meet_le_right _ _) (le_meet _ _ _ h rel_refl),
   fun h => h ▸ meet_le_left _ _⟩
theorem le_iff_meet_eq_left : (P ⊑ Q) ↔ P ⊓ Q = P :=
  ⟨fun h => rel_antisymm (meet_le_left _ _) (le_meet _ _ _ rel_refl h),
   fun h => h ▸ meet_le_right _ _⟩
theorem le_iff_join_eq_left : (P ⊑ Q) ↔ Q ⊔ P = Q :=
  ⟨fun h => rel_antisymm (join_le _ _ _ rel_refl h) (left_le_join _ _),
   fun h => h ▸ right_le_join _ _⟩
theorem le_iff_join_eq_right : (P ⊑ Q) ↔ P ⊔ Q = Q :=
  ⟨fun h => rel_antisymm (join_le _ _ _ h rel_refl) (right_le_join _ _),
   fun h => h ▸ left_le_join _ _⟩

theorem top_meet : (⊤ : l) ⊓ P = P :=
  rel_antisymm (meet_le_right _ _) (le_meet _ _ _ (le_top _) rel_refl)
theorem meet_top : P ⊓ (⊤ : l) = P := meet_comm.trans top_meet
/-- Cancel a redundant `⊓ ⊤` on the left of an entailment. -/
theorem meet_top_le_of_le (h : P ⊑ Q) : P ⊓ ⊤ ⊑ Q := by rw [meet_top]; exact h
theorem bot_meet : (⊥ : l) ⊓ P = ⊥ :=
  rel_antisymm (meet_le_of_left_le (bot_le _)) (bot_le _)
theorem meet_bot : P ⊓ (⊥ : l) = ⊥ := meet_comm.trans bot_meet
theorem top_join : (⊤ : l) ⊔ P = ⊤ :=
  rel_antisymm (le_top _) (left_le_join _ _)
theorem join_top : P ⊔ (⊤ : l) = ⊤ := join_comm.trans top_join
theorem bot_join : (⊥ : l) ⊔ P = P :=
  rel_antisymm (join_le _ _ _ (bot_le _) rel_refl) (right_le_join _ _)
theorem join_bot : P ⊔ (⊥ : l) = P := join_comm.trans bot_join

section Frame
variable [Frame l]

theorem meet_join_left : P ⊓ (Q ⊔ R) = (P ⊓ Q) ⊔ (P ⊓ R) :=
  rel_antisymm
    (meet_join_le_right (le_join_of_le_left rel_refl) (le_join_of_le_right rel_refl))
    (join_le _ _ _ (meet_mono_right (left_le_join _ _)) (meet_mono_right (right_le_join _ _)))
theorem join_meet_left : P ⊔ (Q ⊓ R) = (P ⊔ Q) ⊓ (P ⊔ R) :=
  rel_antisymm
    (join_le _ _ _ (le_meet _ _ _ (left_le_join _ _) (left_le_join _ _))
      (meet_mono (right_le_join _ _) (right_le_join _ _)))
    (meet_join_le_left (le_join_of_le_left (meet_le_left _ _))
      (meet_join_le_right (le_join_of_le_left (meet_le_right _ _)) (le_join_of_le_right rel_refl)))
theorem meet_join_right : (P ⊔ Q) ⊓ R = (P ⊓ R) ⊔ (Q ⊓ R) :=
  meet_comm.trans (meet_join_left.trans (rel_antisymm
    (join_mono (P := _) (Q := _) (P' := _) (Q' := _)
      (rel_of_eq meet_comm) (rel_of_eq meet_comm))
    (join_mono (rel_of_eq meet_comm) (rel_of_eq meet_comm))))
theorem join_meet_right : (P ⊓ Q) ⊔ R = (P ⊔ R) ⊓ (Q ⊔ R) :=
  join_comm.trans (join_meet_left.trans (rel_antisymm
    (meet_mono (rel_of_eq join_comm) (rel_of_eq join_comm))
    (meet_mono (rel_of_eq join_comm) (rel_of_eq join_comm))))

theorem top_himp : ((⊤ : l) ⇨ P) = P :=
  rel_antisymm
    (rel_trans (le_meet _ _ _ (le_top _) rel_refl) meet_himp_le)
    (le_himp (meet_le_of_left_le rel_refl))
theorem le_himp_self : Q ⊑ P ⇨ P := le_himp (meet_le_right _ _)
theorem le_himp_self_iff : (Q ⊑ P ⇨ P) ↔ True := iff_true_intro le_himp_self
theorem himp_meet_himp_le : (P ⇨ Q) ⊓ (Q ⇨ R) ⊑ P ⇨ R :=
  le_himp_of_meet_le_comm <|
    rel_trans (rel_of_eq meet_assoc.symm) <|
      rel_trans (meet_mono_left meet_himp_le) meet_himp_le
theorem bot_himp : ((⊥ : l) ⇨ P) = ⊤ :=
  rel_antisymm (le_top _) (le_himp (meet_le_of_right_le (bot_le _)))

theorem meet_himp_le_meet : P' ⊓ (P' ⇨ Q') ⊑ P' ⊓ Q' :=
  le_meet _ _ _ (meet_le_left _ _) (rel_trans meet_le_comm himp_meet_le)
theorem meet_le_meet_of_le_himp (hp : P ⊑ P') (hq : Q ⊑ (P' ⇨ Q')) : P ⊓ Q ⊑ P' ⊓ Q' :=
  rel_trans (meet_mono hp hq) meet_himp_le_meet

end Frame

/-! # Propositional embedding (`CompleteLattice.ofProp`) -/

theorem ofProp_elim {φ : Prop} (h1 : Q ⊑ (⌜φ⌝ : l)) (h2 : φ → Q ⊑ R) : Q ⊑ R := by
  by_cases hφ : φ
  · exact h2 hφ
  · simp [CompleteLattice.ofProp, hφ] at h1
    exact rel_trans h1 (bot_le _)

theorem ofProp_mono {φ₁ φ₂ : Prop} (h : φ₁ → φ₂) : ⌜φ₁⌝ ⊑ (⌜φ₂⌝ : l) :=
  CompleteLattice.ofProp_imp _ _ h
theorem ofProp_congr {φ₁ φ₂ : Prop} (h : φ₁ ↔ φ₂) : (⌜φ₁⌝ : l) = ⌜φ₂⌝ :=
  rel_antisymm (ofProp_mono h.1) (ofProp_mono h.2)

theorem ofProp_meet_le_left {φ : Prop} (h : φ → Q ⊑ R) : (⌜φ⌝ : l) ⊓ Q ⊑ R := by
  rw [CompleteLattice.ofProp_intro_r]; exact h
theorem ofProp_meet_le_right {φ : Prop} (h : φ → Q ⊑ R) : Q ⊓ (⌜φ⌝ : l) ⊑ R := by
  rw [CompleteLattice.ofProp_intro_l]; exact h
theorem ofProp_eq_top {φ : Prop} (h : φ) : (⌜φ⌝ : l) = ⊤ :=
  (ofProp_congr ⟨fun _ => trivial, fun _ => h⟩).trans (CompleteLattice.ofProp_true l)

theorem ofProp_and {φ₁ φ₂ : Prop} : (⌜φ₁⌝ : l) ⊓ ⌜φ₂⌝ = ⌜φ₁ ∧ φ₂⌝ := by
  apply rel_antisymm
  · apply ofProp_meet_le_right
    intro h₂
    apply ofProp_mono
    exact (⟨·, h₂⟩)
  · exact le_meet _ _ _ (ofProp_mono And.left) (ofProp_mono And.right)

theorem ofProp_or {φ₁ φ₂ : Prop} : (⌜φ₁⌝ : l) ⊔ ⌜φ₂⌝ = ⌜φ₁ ∨ φ₂⌝ := by
  apply rel_antisymm
  · exact join_le _ _ _ (ofProp_mono Or.inl) (ofProp_mono Or.inr)
  · rw [CompleteLattice.ofProp_intro]
    rintro (h₁ | h₂)
    · rw [ofProp_eq_top h₁]
      exact left_le_join _ _
    · rw [ofProp_eq_top h₂]
      exact right_le_join _ _

theorem ofProp_forall_le {α} {Φ : α → Prop} : (⌜∀ x, Φ x⌝ : l) ⊑ iInf (fun x => ⌜Φ x⌝) :=
  le_iInf _ _ fun _ => ofProp_mono (· _)

theorem ofProp_exists {α} {Φ : α → Prop} :
    iSup (fun x => (⌜Φ x⌝ : l)) = ⌜∃ x, Φ x⌝ := by
  apply rel_antisymm
  · exact iSup_le _ _ fun a => ofProp_mono (⟨a, ·⟩)
  · rw [CompleteLattice.ofProp_intro]
    rintro ⟨x, hx⟩
    have h : (⌜Φ x⌝ : l) = ⊤ := ofProp_eq_top hx
    exact h ▸ le_iSup (fun x => (⌜Φ x⌝ : l)) x

theorem ofProp_forall {α} {Φ : α → Prop} :
    iInf (fun x => (⌜Φ x⌝ : l)) = ⌜∀ x, Φ x⌝ := by
  apply rel_antisymm
  · by_cases h : ∃ x, ¬Φ x
    · obtain ⟨x, hx⟩ := h
      exact rel_trans (iInf_le _ x) (ofProp_mono hx.elim)
    · have hall : ∀ x, Φ x := fun x => Classical.not_not.1 <| mt (⟨x, ·⟩) h
      have heq : (⌜∀ x, Φ x⌝ : l) = ⊤ := ofProp_eq_top hall
      exact heq ▸ le_top _
  · exact ofProp_forall_le

section Frame
variable [Frame l]

theorem himp_ofProp_le {φ₁ φ₂ : Prop} : (⌜φ₁ → φ₂⌝ : l) ⊑ (⌜φ₁⌝ ⇨ ⌜φ₂⌝) :=
  le_himp (rel_trans (rel_of_eq ofProp_and) (ofProp_mono (And.elim id)))

theorem himp_ofProp {φ₁ φ₂ : Prop} : ((⌜φ₁⌝ : l) ⇨ ⌜φ₂⌝) = ⌜φ₁ → φ₂⌝ := by
  apply rel_antisymm
  · by_cases h₁ : φ₁
    · -- φ₁ true: weaken the LHS to `(⌜φ₁⌝ ⇨ ⌜φ₂⌝) ⊓ ⌜φ₁⌝` and apply `himp_meet_le`.
      have h₁' : (⊤ : l) ⊑ ⌜φ₁⌝ := by
        have : (⌜φ₁⌝ : l) = ⊤ := ofProp_eq_top h₁
        exact this ▸ rel_refl
      exact rel_trans
        (le_meet _ _ _ rel_refl (rel_trans (le_top _) h₁'))
        (rel_trans himp_meet_le (ofProp_mono (fun h _ => h)))
    · -- φ₁ false: `⌜φ₁ → φ₂⌝ = ⊤`
      have : (⌜φ₁ → φ₂⌝ : l) = ⊤ := ofProp_eq_top (fun hp => absurd hp h₁)
      exact this ▸ le_top _
  · exact himp_ofProp_le

end Frame

/-! # Miscellaneous -/

theorem meet_left_comm : P ⊓ (Q ⊓ R) = Q ⊓ (P ⊓ R) := by
  rw [← meet_assoc, meet_comm (P := P), meet_assoc]
theorem meet_right_comm : (P ⊓ Q) ⊓ R = (P ⊓ R) ⊓ Q := by
  rw [meet_assoc, meet_comm (P := Q), ← meet_assoc]

/-! # Working with entailment -/

/-- `⊤ ⊑ (P ⇨ Q)` iff `P ⊑ Q`. -/
@[simp] theorem top_le_himp_iff [Frame l] (P Q : l) :
    ((⊤ : l) ⊑ P ⇨ Q) ↔ (P ⊑ Q) :=
  ⟨fun h => rel_trans
    (le_meet _ _ _ (le_top _) rel_refl)
    (rel_trans (meet_mono_left h) himp_meet_le),
   fun h => le_himp (meet_le_of_right_le h)⟩

@[simp] theorem le_top_iff : (Q ⊑ (⊤ : l)) ↔ True := iff_true_intro (le_top _)

/-! ## Pointwise unfoldings of `⊑` on function lattices

Fixed-arity instances of `le_iff_forall_le` for nested function lattices, stated separately per
arity so that `simp` and `grind` can apply them. Each is definitional via the function-space
`PartialOrder` instance. -/

@[simp] theorem le_iff_forall_le_1 {σ : Type v} {P Q : σ → l} :
    P ⊑ Q ↔ ∀ s, P s ⊑ Q s := Iff.rfl
@[simp] theorem le_iff_forall_le_2 {σ₁ σ₂ : Type v} {P Q : σ₁ → σ₂ → l} :
    P ⊑ Q ↔ ∀ s₁ s₂, P s₁ s₂ ⊑ Q s₁ s₂ := Iff.rfl
@[simp] theorem le_iff_forall_le_3 {σ₁ σ₂ σ₃ : Type v} {P Q : σ₁ → σ₂ → σ₃ → l} :
    P ⊑ Q ↔ ∀ s₁ s₂ s₃, P s₁ s₂ s₃ ⊑ Q s₁ s₂ s₃ := Iff.rfl
@[simp] theorem le_iff_forall_le_4 {σ₁ σ₂ σ₃ σ₄ : Type v} {P Q : σ₁ → σ₂ → σ₃ → σ₄ → l} :
    P ⊑ Q ↔ ∀ s₁ s₂ s₃ s₄, P s₁ s₂ s₃ s₄ ⊑ Q s₁ s₂ s₃ s₄ := Iff.rfl
@[simp] theorem le_iff_forall_le_5 {σ₁ σ₂ σ₃ σ₄ σ₅ : Type v} {P Q : σ₁ → σ₂ → σ₃ → σ₄ → σ₅ → l} :
    P ⊑ Q ↔ ∀ s₁ s₂ s₃ s₄ s₅, P s₁ s₂ s₃ s₄ s₅ ⊑ Q s₁ s₂ s₃ s₄ s₅ := Iff.rfl

end Std.Internal.Do.CompleteLattice
