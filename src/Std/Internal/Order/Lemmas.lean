/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Gladshtein, Sebastian Graf
-/
module

prelude
public import Std.Internal.Order.Basic
public import Init.ByCases
import Init.Classical
import Init.TacticsExtra

@[expose] public section

/-!
# Complete lattice algebra

The laws of `⊤`, `⊥`, `⊓`, `⊔`, `⨅` and `⨆` at an abstract carrier: the order laws, the units, the
monoid laws of `⊓` and `⊔`, monotonicity, and the characterizations of `⊑` against the connectives.
-/

namespace Lean.Order

section CompleteLattice

open PartialOrder Std.Internal.Order

universe uₗ vₗ wₗ

variable {α : Type uₗ} [CompleteLattice α]

theorem le_top (x : α) : x ⊑ ⊤ := by
  apply le_sup
  trivial

theorem meet_le_left (x y : α) : x ⊓ y ⊑ x := by
  apply inf_le
  left; rfl

theorem meet_le_right (x y : α) : x ⊓ y ⊑ y := by
  apply inf_le
  right; rfl

theorem le_meet (x y z : α) : x ⊑ y → x ⊑ z → x ⊑ y ⊓ z := by
  intro hxy hxz
  apply le_inf
  intro w hw
  cases hw with
  | inl h => rw [h]; exact hxy
  | inr h => rw [h]; exact hxz

theorem left_le_join (x y : α) : x ⊑ x ⊔ y := by
  apply le_sup
  left; rfl

theorem right_le_join (x y : α) : y ⊑ x ⊔ y := by
  apply le_sup
  right; rfl

theorem join_le (x y z : α) : x ⊑ z → y ⊑ z → x ⊔ y ⊑ z := by
  intro hxz hyz
  apply sup_le
  intro w hw
  cases hw with
  | inl h => rw [h]; exact hxz
  | inr h => rw [h]; exact hyz

theorem iInf_le {ι : Sort vₗ} (f : ι → α) (i : ι) : iInf f ⊑ f i := by
  apply inf_le
  exact ⟨i, rfl⟩

theorem le_iInf {ι : Sort vₗ} (f : ι → α) (x : α) : (∀ i, x ⊑ f i) → x ⊑ iInf f := by
  intro h
  apply le_inf
  intro y ⟨i, hi⟩
  rw [← hi]
  exact h i

theorem le_iSup {ι : Sort vₗ} (f : ι → α) (i : ι) : f i ⊑ iSup f := by
  apply le_sup
  exact ⟨i, rfl⟩

theorem iSup_le {ι : Sort vₗ} (f : ι → α) (x : α) : (∀ i, f i ⊑ x) → iSup f ⊑ x := by
  intro h
  apply sup_le
  intro y ⟨i, hi⟩
  rw [← hi]
  exact h i

end CompleteLattice

/-! ## Derived laws of `CompleteLattice`

Lattice algebra derived from the laws of `CompleteLattice`: monotonicity of the connectives, the
monoid laws of `⊓` and `⊔` with their units `⊤` and `⊥`, and the characterizations of `⊑` against
`⊤`, `⊥`, `⊓`, `⊔`, `⨅` and `⨆`.
-/

section CompleteLatticeAlgebra

open PartialOrder

set_option linter.unusedSectionVars false

universe uₗ vₗ

variable {l : Type uₗ} [CompleteLattice l] {P P' Q Q' R R' T : l}

/-! ### Connectives -/

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
theorem le_of_le_of_meet_le (h₁ : P ⊑ Q) (h₂ : P ⊓ Q ⊑ R) : P ⊑ R :=
  rel_trans (le_meet _ _ _ rel_refl h₁) h₂
theorem le_iSup_of_le {β} {Ψ : β → l} (a : β) (h : P ⊑ Ψ a) : P ⊑ iSup Ψ :=
  rel_trans h (le_iSup _ a)
theorem le_of_le_bot (h : P ⊑ (⊥ : l)) : P ⊑ Q := rel_trans h (bot_le _)

/-! ### Monotonicity -/

theorem meet_mono (hp : P ⊑ P') (hq : Q ⊑ Q') : P ⊓ Q ⊑ P' ⊓ Q' :=
  le_meet _ _ _ (meet_le_of_left_le hp) (meet_le_of_right_le hq)
theorem meet_mono_left (h : P ⊑ P') : P ⊓ Q ⊑ P' ⊓ Q := meet_mono h rel_refl
theorem meet_mono_right (h : Q ⊑ Q') : P ⊓ Q ⊑ P ⊓ Q' := meet_mono rel_refl h

theorem join_mono (hp : P ⊑ P') (hq : Q ⊑ Q') : P ⊔ Q ⊑ P' ⊔ Q' :=
  join_le _ _ _ (le_join_of_le_left hp) (le_join_of_le_right hq)
theorem join_mono_left (h : P ⊑ P') : P ⊔ Q ⊑ P' ⊔ Q := join_mono h rel_refl
theorem join_mono_right (h : Q ⊑ Q') : P ⊔ Q ⊑ P ⊔ Q' := join_mono rel_refl h

theorem iInf_mono {β} {Φ Ψ : β → l} (h : ∀ a, Φ a ⊑ Ψ a) : iInf Φ ⊑ iInf Ψ :=
  le_iInf _ _ fun a => rel_trans (iInf_le _ a) (h a)
theorem iSup_mono {β} {Φ Ψ : β → l} (h : ∀ a, Φ a ⊑ Ψ a) : iSup Φ ⊑ iSup Ψ :=
  iSup_le _ _ fun a => rel_trans (h a) (le_iSup _ a)

/-! ### Boolean algebra -/

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
theorem iSup_bot {ι : Type _} : (⨆ _ : ι, (⊥ : l)) = ⊥ :=
  rel_antisymm (iSup_le _ _ fun _ => rel_refl) (bot_le _)
theorem iInf_top {ι : Type _} : (⨅ _ : ι, (⊤ : l)) = ⊤ :=
  rel_antisymm (le_top _) (le_iInf _ _ fun _ => rel_refl)

/-! ### Miscellaneous -/

theorem meet_left_comm : P ⊓ (Q ⊓ R) = Q ⊓ (P ⊓ R) := by
  rw [← meet_assoc, meet_comm (P := P), meet_assoc]
theorem meet_right_comm : (P ⊓ Q) ⊓ R = (P ⊓ R) ⊓ Q := by
  rw [meet_assoc, meet_comm (P := Q), ← meet_assoc]

/-! ### Working with entailment -/

theorem le_top_iff : (Q ⊑ (⊤ : l)) ↔ True := iff_true_intro (le_top _)
theorem bot_le_iff : ((⊥ : l) ⊑ Q) ↔ True := iff_true_intro (bot_le _)
theorem join_le_iff : (P ⊔ Q ⊑ R) ↔ (P ⊑ R ∧ Q ⊑ R) :=
  ⟨fun h => ⟨rel_trans (left_le_join _ _) h, rel_trans (right_le_join _ _) h⟩,
   fun h => join_le _ _ _ h.1 h.2⟩
theorem le_meet_iff : (P ⊑ Q ⊓ R) ↔ (P ⊑ Q ∧ P ⊑ R) :=
  ⟨fun h => ⟨rel_trans h (meet_le_left _ _), rel_trans h (meet_le_right _ _)⟩,
   fun h => le_meet _ _ _ h.1 h.2⟩
theorem iSup_le_iff {ι : Type _} {Φ : ι → l} : (iSup Φ ⊑ P) ↔ ∀ i, Φ i ⊑ P :=
  ⟨fun h i => rel_trans (le_iSup _ i) h, iSup_le _ _⟩
theorem le_iInf_iff {ι : Type _} {Φ : ι → l} : (P ⊑ iInf Φ) ↔ ∀ i, P ⊑ Φ i :=
  ⟨fun h i => rel_trans h (iInf_le _ i), le_iInf _ _⟩

@[deprecated le_of_le_of_meet_le (since := "2026-09-24")]
theorem le_trans_meet (h₁ : P ⊑ Q) (h₂ : P ⊓ Q ⊑ R) : P ⊑ R := le_of_le_of_meet_le h₁ h₂

end CompleteLatticeAlgebra

end Lean.Order
