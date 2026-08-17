/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Gladshtein, Sebastian Graf
-/
module

prelude
public import Std.Internal.Order.Lemmas
public import Init.ByCases
import Init.Classical
universe u v
@[expose] public section

set_option linter.missingDocs true

/-!
# Embedding of propositions into a complete lattice

`⌜p⌝` embeds a proposition `p` into an assertion lattice as `⊤` if `p` holds and `⊥` otherwise.
-/

open Classical

namespace Lean.Order

open PartialOrder Std.Internal.Order

/-- Embedding of propositions into an CompleteLattice type. `⌜p⌝` embeds `p : Prop` as `⊤` if `p` holds
and `⊥` otherwise. -/
noncomputable def CompleteLattice.ofProp [CompleteLattice l] (p : Prop) : l :=
  if p then ⊤ else ⊥

@[inherit_doc CompleteLattice.ofProp]
scoped notation "⌜" p "⌝" => CompleteLattice.ofProp p

@[simp]
theorem CompleteLattice.ofProp_true (l : Type v) [CompleteLattice l] : ⌜True⌝ = (⊤ : l) := by
  simp [CompleteLattice.ofProp]

@[simp]
theorem CompleteLattice.ofProp_false (l : Type v) [CompleteLattice l] : ⌜False⌝ = (⊥ : l) := by
  simp [CompleteLattice.ofProp]

@[grind .]
theorem CompleteLattice.ofProp_imp [CompleteLattice l]
  (p₁ p₂ : Prop) : (p₁ → p₂) → ⌜p₁⌝ ⊑ (⌜p₂⌝ : l) := by
  simp only [CompleteLattice.ofProp]
  intro h
  split
  case isTrue hp1 =>
    split
    case isTrue => exact PartialOrder.rel_refl
    case isFalse hp2 => exact absurd (h hp1) hp2
  case isFalse =>
    exact bot_le _

@[simp]
theorem CompleteLattice.ofProp_intro [CompleteLattice l]
  (p : Prop) (h : l) : (⌜p⌝ ⊑ h) = (p → ⊤ ⊑ h) := by
  simp only [CompleteLattice.ofProp]
  apply propext
  constructor
  · intro hle hp
    simp only [hp, ↓reduceIte] at hle
    exact hle
  · intro himp
    split
    next hp => exact himp hp
    next => exact bot_le _

@[simp]
theorem CompleteLattice.ofProp_intro_l [CompleteLattice l] (p : Prop) (x y : l) :
  (x ⊓ ⌜ p ⌝ ⊑ y) = (p → x ⊑ y) := by
  apply propext
  constructor
  · intro h hp
    have hxy : x ⊓ ⊤ ⊑ y := by simp only [CompleteLattice.ofProp, hp, ↓reduceIte] at h; exact h
    have hx_le_meet : x ⊑ x ⊓ ⊤ := le_meet x x ⊤ PartialOrder.rel_refl (le_top x)
    exact PartialOrder.rel_trans hx_le_meet hxy
  · intro h
    simp only [CompleteLattice.ofProp]
    split
    next hp => exact PartialOrder.rel_trans (meet_le_left x ⊤) (h hp)
    next => exact PartialOrder.rel_trans (meet_le_right x ⊥) (bot_le _)

@[simp]
theorem CompleteLattice.ofProp_intro_r [CompleteLattice l] (p : Prop) (x y : l) :
  (⌜ p ⌝ ⊓ x ⊑ y) = (p → x ⊑ y) := by
  apply propext
  constructor
  · intro h hp
    have hxy : ⊤ ⊓ x ⊑ y := by simp only [CompleteLattice.ofProp, hp, ↓reduceIte] at h; exact h
    have hx_le_meet : x ⊑ ⊤ ⊓ x := le_meet x ⊤ x (le_top x) PartialOrder.rel_refl
    exact PartialOrder.rel_trans hx_le_meet hxy
  · intro h
    simp only [CompleteLattice.ofProp]
    split
    next hp => exact PartialOrder.rel_trans (meet_le_right ⊤ x) (h hp)
    next => exact PartialOrder.rel_trans (meet_le_left ⊥ x) (bot_le _)

/-- Pointwise characterization of `CompleteLattice.ofProp` on a function lattice. -/
@[simp] theorem CompleteLattice.ofProp_apply
    {σ : Type v} {β : Type u} [CompleteLattice β] (p : Prop) (s : σ) :
    (⌜p⌝ : σ → β) s = (⌜p⌝ : β) := by
  simp only [CompleteLattice.ofProp]
  rcases Classical.em p with h | h <;> simp [h]

@[grind .]
theorem top_le_ofProp [CompleteLattice l] (p : Prop) : p → (⊤ : l) ⊑ ⌜p⌝ := by
  simp only [CompleteLattice.ofProp]
  rcases Classical.em p with h | h <;> simp [h]

/-- `x ⊑ ⌜p⌝` whenever `p` holds. -/
theorem le_ofProp [CompleteLattice l] (x : l) (p : Prop) : p → x ⊑ ⌜p⌝ :=
  fun hp => PartialOrder.rel_trans (le_top x) (top_le_ofProp p hp)

/-- `⌜p⌝ ⊑ rhs` reduces to assuming `p` and proving `⊤ ⊑ rhs`. -/
theorem ofProp_le [CompleteLattice l] (p : Prop) (rhs : l) :
    (p → (⊤ : l) ⊑ rhs) → ⌜p⌝ ⊑ rhs :=
  (CompleteLattice.ofProp_intro p rhs).mpr

/-- `⌜p⌝ ⊓ x ⊑ rhs` reduces to assuming `p` and proving `x ⊑ rhs`. -/
theorem ofProp_meet_le [CompleteLattice l] (p : Prop) (x rhs : l) :
    (p → x ⊑ rhs) → ⌜p⌝ ⊓ x ⊑ rhs :=
  (CompleteLattice.ofProp_intro_r p x rhs).mpr

/-- Embedding a proposition into the `Prop` lattice (`⌜p⌝`) is the proposition itself. -/
@[grind =, simp] theorem ofProp_prop_eq (p : Prop) : (⌜p⌝ : Prop) = p := by
  simp only [CompleteLattice.ofProp]
  rcases Classical.em p with hp | hp <;> simp [hp, top_prop_eq, bot_prop_eq]

/-! `Prop`-valued, fixed-arity specializations of `CompleteLattice.ofProp_apply`: `⌜p⌝` at a
state-indexed `Prop` lattice, applied to its states, is `p`. Fixing the carrier to `Prop` (a ground
instance) leaves every parameter recoverable from the trigger, so these are usable `@[grind =]`
lemmas where the general `ofProp_apply` is not. They reduce a guard straight to its `Prop` in one
step, avoiding the intermediate `(⌜p⌝ : Prop)` whose instance `ofProp_prop_eq` fails to match. -/

@[grind =] theorem CompleteLattice.ofProp_apply_1 {σ₁ : Type _}
    (p : Prop) (s₁ : σ₁) : (⌜p⌝ : σ₁ → Prop) s₁ = p := by
  simp only [CompleteLattice.ofProp_apply, ofProp_prop_eq]

@[grind =] theorem CompleteLattice.ofProp_apply_2 {σ₁ : Type _} {σ₂ : Type _}
    (p : Prop) (s₁ : σ₁) (s₂ : σ₂) : (⌜p⌝ : σ₁ → σ₂ → Prop) s₁ s₂ = p := by
  simp only [CompleteLattice.ofProp_apply, ofProp_prop_eq]

@[grind =] theorem CompleteLattice.ofProp_apply_3 {σ₁ : Type _} {σ₂ : Type _} {σ₃ : Type _}
    (p : Prop) (s₁ : σ₁) (s₂ : σ₂) (s₃ : σ₃) : (⌜p⌝ : σ₁ → σ₂ → σ₃ → Prop) s₁ s₂ s₃ = p := by
  simp only [CompleteLattice.ofProp_apply, ofProp_prop_eq]

@[grind =] theorem CompleteLattice.ofProp_apply_4 {σ₁ : Type _} {σ₂ : Type _} {σ₃ : Type _}
    {σ₄ : Type _} (p : Prop) (s₁ : σ₁) (s₂ : σ₂) (s₃ : σ₃) (s₄ : σ₄) :
    (⌜p⌝ : σ₁ → σ₂ → σ₃ → σ₄ → Prop) s₁ s₂ s₃ s₄ = p := by
  simp only [CompleteLattice.ofProp_apply, ofProp_prop_eq]

@[grind =] theorem CompleteLattice.ofProp_apply_5 {σ₁ : Type _} {σ₂ : Type _} {σ₃ : Type _}
    {σ₄ : Type _} {σ₅ : Type _} (p : Prop) (s₁ : σ₁) (s₂ : σ₂) (s₃ : σ₃) (s₄ : σ₄) (s₅ : σ₅) :
    (⌜p⌝ : σ₁ → σ₂ → σ₃ → σ₄ → σ₅ → Prop) s₁ s₂ s₃ s₄ s₅ = p := by
  simp only [CompleteLattice.ofProp_apply, ofProp_prop_eq]

section Lemmas

set_option linter.unusedSectionVars false

variable {l : Type u} [CompleteLattice l] {P P' Q Q' R R' T : l} {φ φ₁ φ₂ : Prop}

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

theorem ofProp_forall_le {β} {Φ : β → Prop} : (⌜∀ x, Φ x⌝ : l) ⊑ iInf (fun x => ⌜Φ x⌝) :=
  le_iInf _ _ fun _ => ofProp_mono (· _)

theorem ofProp_exists {β} {Φ : β → Prop} :
    iSup (fun x => (⌜Φ x⌝ : l)) = ⌜∃ x, Φ x⌝ := by
  apply rel_antisymm
  · exact iSup_le _ _ fun a => ofProp_mono (⟨a, ·⟩)
  · rw [CompleteLattice.ofProp_intro]
    rintro ⟨x, hx⟩
    have h : (⌜Φ x⌝ : l) = ⊤ := ofProp_eq_top hx
    exact h ▸ le_iSup (fun x => (⌜Φ x⌝ : l)) x

theorem ofProp_forall {β} {Φ : β → Prop} :
    iInf (fun x => (⌜Φ x⌝ : l)) = ⌜∀ x, Φ x⌝ := by
  apply rel_antisymm
  · by_cases h : ∃ x, ¬Φ x
    · obtain ⟨x, hx⟩ := h
      exact rel_trans (iInf_le _ x) (ofProp_mono hx.elim)
    · have hall : ∀ x, Φ x := fun x => Classical.not_not.1 <| mt (⟨x, ·⟩) h
      have heq : (⌜∀ x, Φ x⌝ : l) = ⊤ := ofProp_eq_top hall
      exact heq ▸ le_top _
  · exact ofProp_forall_le

end Lemmas

end Lean.Order

end -- public section
