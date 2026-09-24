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

theorem CompleteLattice.ofProp_true (l : Type v) [CompleteLattice l] : ⌜True⌝ = (⊤ : l) := by
  simp [CompleteLattice.ofProp]

theorem CompleteLattice.ofProp_false (l : Type v) [CompleteLattice l] : ⌜False⌝ = (⊥ : l) := by
  simp [CompleteLattice.ofProp]

theorem CompleteLattice.ofProp_le_eq_imp [CompleteLattice l]
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

theorem CompleteLattice.meet_ofProp_le_eq_imp [CompleteLattice l] (p : Prop) (x y : l) :
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

theorem CompleteLattice.ofProp_meet_le_eq_imp [CompleteLattice l] (p : Prop) (x y : l) :
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
theorem CompleteLattice.ofProp_apply
    {σ : Type v} {β : Type u} [CompleteLattice β] (p : Prop) (s : σ) :
    (⌜p⌝ : σ → β) s = (⌜p⌝ : β) := by
  simp only [CompleteLattice.ofProp]
  rcases Classical.em p with h | h <;> simp [h, top_apply, bot_apply]

theorem CompleteLattice.top_le_ofProp [CompleteLattice l] (p : Prop) : p → (⊤ : l) ⊑ ⌜p⌝ := by
  intro hp
  simp only [CompleteLattice.ofProp, hp, ↓reduceIte]
  exact PartialOrder.rel_refl

theorem CompleteLattice.top_le_ofProp_iff [CompleteLattice l] (p : Prop) :
    ((⊤ : l) ⊑ ⌜p⌝) ↔ (p ∨ (⊤ : l) ⊑ ⊥) := by
  constructor
  · intro h
    by_cases hp : p
    · exact .inl hp
    · refine .inr ?_
      simpa only [CompleteLattice.ofProp, hp, ↓reduceIte] using h
  · rintro (hp | h)
    · exact top_le_ofProp p hp
    · exact rel_trans h (bot_le _)

/-- `x ⊑ ⌜p⌝` whenever `p` holds. -/
theorem CompleteLattice.le_ofProp [CompleteLattice l] (x : l) (p : Prop) : p → x ⊑ ⌜p⌝ :=
  fun hp => PartialOrder.rel_trans (le_top x) (top_le_ofProp p hp)

/-- `⌜p⌝ ⊑ rhs` reduces to assuming `p` and proving `⊤ ⊑ rhs`. -/
theorem CompleteLattice.ofProp_le [CompleteLattice l] (p : Prop) (rhs : l) :
    (p → (⊤ : l) ⊑ rhs) → ⌜p⌝ ⊑ rhs :=
  (CompleteLattice.ofProp_le_eq_imp p rhs).mpr

/-- Embedding a proposition into the `Prop` lattice (`⌜p⌝`) is the proposition itself. -/
theorem CompleteLattice.ofProp_prop_eq (p : Prop) : (⌜p⌝ : Prop) = p := by
  simp only [CompleteLattice.ofProp]
  rcases Classical.em p with hp | hp <;> simp [hp, top_prop_eq, bot_prop_eq]

@[deprecated CompleteLattice.ofProp_apply +typeChanged (since := "2026-09-24")]
theorem CompleteLattice.ofProp_apply_1 {σ1 : Type _}
    (p : Prop) (s1 : σ1) :
    (⌜p⌝ : σ1 → Prop) s1 = p := by
  simp only [CompleteLattice.ofProp_apply, ofProp_prop_eq]

@[deprecated CompleteLattice.ofProp_apply +typeChanged (since := "2026-09-24")]
theorem CompleteLattice.ofProp_apply_2 {σ1 : Type _} {σ2 : Type _}
    (p : Prop) (s1 : σ1) (s2 : σ2) :
    (⌜p⌝ : σ1 → σ2 → Prop) s1 s2 = p := by
  simp only [CompleteLattice.ofProp_apply, ofProp_prop_eq]

@[deprecated CompleteLattice.ofProp_apply +typeChanged (since := "2026-09-24")]
theorem CompleteLattice.ofProp_apply_3 {σ1 : Type _} {σ2 : Type _} {σ3 : Type _}
    (p : Prop) (s1 : σ1) (s2 : σ2) (s3 : σ3) :
    (⌜p⌝ : σ1 → σ2 → σ3 → Prop) s1 s2 s3 = p := by
  simp only [CompleteLattice.ofProp_apply, ofProp_prop_eq]

@[deprecated CompleteLattice.ofProp_apply +typeChanged (since := "2026-09-24")]
theorem CompleteLattice.ofProp_apply_4 {σ1 : Type _} {σ2 : Type _} {σ3 : Type _} {σ4 : Type _}
    (p : Prop) (s1 : σ1) (s2 : σ2) (s3 : σ3) (s4 : σ4) :
    (⌜p⌝ : σ1 → σ2 → σ3 → σ4 → Prop) s1 s2 s3 s4 = p := by
  simp only [CompleteLattice.ofProp_apply, ofProp_prop_eq]

@[deprecated CompleteLattice.ofProp_apply +typeChanged (since := "2026-09-24")]
theorem CompleteLattice.ofProp_apply_5 {σ1 : Type _} {σ2 : Type _} {σ3 : Type _} {σ4 : Type _} {σ5 : Type _}
    (p : Prop) (s1 : σ1) (s2 : σ2) (s3 : σ3) (s4 : σ4) (s5 : σ5) :
    (⌜p⌝ : σ1 → σ2 → σ3 → σ4 → σ5 → Prop) s1 s2 s3 s4 s5 = p := by
  simp only [CompleteLattice.ofProp_apply, ofProp_prop_eq]

@[deprecated CompleteLattice.top_le_ofProp (since := "2026-09-24")]
theorem top_le_ofProp [CompleteLattice l] (p : Prop) : p → (⊤ : l) ⊑ ⌜p⌝ :=
  CompleteLattice.top_le_ofProp p
@[deprecated CompleteLattice.le_ofProp (since := "2026-09-24")]
theorem le_ofProp [CompleteLattice l] (x : l) (p : Prop) : p → x ⊑ ⌜p⌝ :=
  CompleteLattice.le_ofProp x p
@[deprecated CompleteLattice.ofProp_le (since := "2026-09-24")]
theorem ofProp_le [CompleteLattice l] (p : Prop) (rhs : l) :
    (p → (⊤ : l) ⊑ rhs) → ⌜p⌝ ⊑ rhs :=
  CompleteLattice.ofProp_le p rhs
@[deprecated CompleteLattice.ofProp_prop_eq (since := "2026-09-24")]
theorem ofProp_prop_eq (p : Prop) : (⌜p⌝ : Prop) = p :=
  CompleteLattice.ofProp_prop_eq p
@[deprecated CompleteLattice.ofProp_le_eq_imp (since := "2026-09-24")]
theorem CompleteLattice.ofProp_intro [CompleteLattice l]
    (p : Prop) (h : l) : (⌜p⌝ ⊑ h) = (p → ⊤ ⊑ h) :=
  CompleteLattice.ofProp_le_eq_imp p h
@[deprecated CompleteLattice.meet_ofProp_le_eq_imp (since := "2026-09-24")]
theorem CompleteLattice.ofProp_intro_l [CompleteLattice l] (p : Prop) (x y : l) :
    (x ⊓ ⌜ p ⌝ ⊑ y) = (p → x ⊑ y) :=
  CompleteLattice.meet_ofProp_le_eq_imp p x y
@[deprecated CompleteLattice.ofProp_meet_le_eq_imp (since := "2026-09-24")]
theorem CompleteLattice.ofProp_intro_r [CompleteLattice l] (p : Prop) (x y : l) :
    (⌜ p ⌝ ⊓ x ⊑ y) = (p → x ⊑ y) :=
  CompleteLattice.ofProp_meet_le_eq_imp p x y

section Lemmas

set_option linter.unusedSectionVars false

variable {l : Type u} [CompleteLattice l] {P P' Q Q' R R' T : l} {φ φ₁ φ₂ : Prop}

theorem CompleteLattice.le_of_le_ofProp {φ : Prop} (h1 : Q ⊑ (⌜φ⌝ : l)) (h2 : φ → Q ⊑ R) : Q ⊑ R := by
  by_cases hφ : φ
  · exact h2 hφ
  · simp [CompleteLattice.ofProp, hφ] at h1
    exact rel_trans h1 (bot_le _)

theorem CompleteLattice.ofProp_mono {φ₁ φ₂ : Prop} (h : φ₁ → φ₂) : ⌜φ₁⌝ ⊑ (⌜φ₂⌝ : l) := by
  simp only [CompleteLattice.ofProp]
  split
  case isTrue hp1 =>
    split
    case isTrue => exact PartialOrder.rel_refl
    case isFalse hp2 => exact absurd (h hp1) hp2
  case isFalse =>
    exact bot_le _
@[deprecated CompleteLattice.ofProp_mono (since := "2026-09-24")]
theorem CompleteLattice.ofProp_imp (p₁ p₂ : Prop) : (p₁ → p₂) → ⌜p₁⌝ ⊑ (⌜p₂⌝ : l) :=
  ofProp_mono
theorem CompleteLattice.ofProp_congr {φ₁ φ₂ : Prop} (h : φ₁ ↔ φ₂) : (⌜φ₁⌝ : l) = ⌜φ₂⌝ :=
  rel_antisymm (ofProp_mono h.1) (ofProp_mono h.2)

theorem CompleteLattice.ofProp_meet_le {φ : Prop} (h : φ → Q ⊑ R) : (⌜φ⌝ : l) ⊓ Q ⊑ R := by
  rw [CompleteLattice.ofProp_meet_le_eq_imp]; exact h
theorem CompleteLattice.meet_ofProp_le {φ : Prop} (h : φ → Q ⊑ R) : Q ⊓ (⌜φ⌝ : l) ⊑ R := by
  rw [CompleteLattice.meet_ofProp_le_eq_imp]; exact h
theorem CompleteLattice.ofProp_eq_top {φ : Prop} (h : φ) : (⌜φ⌝ : l) = ⊤ :=
  (ofProp_congr ⟨fun _ => trivial, fun _ => h⟩).trans (CompleteLattice.ofProp_true l)

theorem CompleteLattice.ofProp_meet_ofProp {φ₁ φ₂ : Prop} : (⌜φ₁⌝ : l) ⊓ ⌜φ₂⌝ = ⌜φ₁ ∧ φ₂⌝ := by
  apply rel_antisymm
  · apply meet_ofProp_le
    intro h₂
    apply ofProp_mono
    exact (⟨·, h₂⟩)
  · exact le_meet _ _ _ (ofProp_mono And.left) (ofProp_mono And.right)

theorem CompleteLattice.ofProp_join_ofProp {φ₁ φ₂ : Prop} : (⌜φ₁⌝ : l) ⊔ ⌜φ₂⌝ = ⌜φ₁ ∨ φ₂⌝ := by
  apply rel_antisymm
  · exact join_le _ _ _ (ofProp_mono Or.inl) (ofProp_mono Or.inr)
  · rw [CompleteLattice.ofProp_le_eq_imp]
    rintro (h₁ | h₂)
    · rw [ofProp_eq_top h₁]
      exact left_le_join _ _
    · rw [ofProp_eq_top h₂]
      exact right_le_join _ _

theorem CompleteLattice.ofProp_forall_le {β} {Φ : β → Prop} :
    (⌜∀ x, Φ x⌝ : l) ⊑ iInf (fun x => ⌜Φ x⌝) :=
  le_iInf _ _ fun _ => ofProp_mono (· _)

theorem CompleteLattice.iSup_ofProp {β} {Φ : β → Prop} :
    iSup (fun x => (⌜Φ x⌝ : l)) = ⌜∃ x, Φ x⌝ := by
  apply rel_antisymm
  · exact iSup_le _ _ fun a => ofProp_mono (⟨a, ·⟩)
  · rw [CompleteLattice.ofProp_le_eq_imp]
    rintro ⟨x, hx⟩
    have h : (⌜Φ x⌝ : l) = ⊤ := ofProp_eq_top hx
    exact h ▸ le_iSup (fun x => (⌜Φ x⌝ : l)) x

theorem CompleteLattice.iInf_ofProp {β} {Φ : β → Prop} :
    iInf (fun x => (⌜Φ x⌝ : l)) = ⌜∀ x, Φ x⌝ := by
  apply rel_antisymm
  · by_cases h : ∃ x, ¬Φ x
    · obtain ⟨x, hx⟩ := h
      exact rel_trans (iInf_le _ x) (ofProp_mono hx.elim)
    · have hall : ∀ x, Φ x := fun x => Classical.not_not.1 <| mt (⟨x, ·⟩) h
      have heq : (⌜∀ x, Φ x⌝ : l) = ⊤ := ofProp_eq_top hall
      exact heq ▸ le_top _
  · exact ofProp_forall_le

@[deprecated CompleteLattice.le_of_le_ofProp (since := "2026-09-24")]
theorem ofProp_elim {φ : Prop} (h1 : Q ⊑ (⌜φ⌝ : l)) (h2 : φ → Q ⊑ R) : Q ⊑ R :=
  CompleteLattice.le_of_le_ofProp h1 h2
@[deprecated CompleteLattice.ofProp_mono (since := "2026-09-24")]
theorem ofProp_mono {φ₁ φ₂ : Prop} (h : φ₁ → φ₂) : ⌜φ₁⌝ ⊑ (⌜φ₂⌝ : l) :=
  CompleteLattice.ofProp_mono h
@[deprecated CompleteLattice.ofProp_congr (since := "2026-09-24")]
theorem ofProp_congr {φ₁ φ₂ : Prop} (h : φ₁ ↔ φ₂) : (⌜φ₁⌝ : l) = ⌜φ₂⌝ :=
  CompleteLattice.ofProp_congr h
@[deprecated CompleteLattice.ofProp_meet_le +typeChanged (since := "2026-09-24")]
theorem ofProp_meet_le (p : Prop) (x rhs : l) :
    (p → x ⊑ rhs) → ⌜p⌝ ⊓ x ⊑ rhs :=
  CompleteLattice.ofProp_meet_le
@[deprecated CompleteLattice.ofProp_meet_le (since := "2026-09-24")]
theorem ofProp_meet_le_left {φ : Prop} (h : φ → Q ⊑ R) : (⌜φ⌝ : l) ⊓ Q ⊑ R :=
  CompleteLattice.ofProp_meet_le h
@[deprecated CompleteLattice.meet_ofProp_le (since := "2026-09-24")]
theorem ofProp_meet_le_right {φ : Prop} (h : φ → Q ⊑ R) : Q ⊓ (⌜φ⌝ : l) ⊑ R :=
  CompleteLattice.meet_ofProp_le h
@[deprecated CompleteLattice.ofProp_eq_top (since := "2026-09-24")]
theorem ofProp_eq_top {φ : Prop} (h : φ) : (⌜φ⌝ : l) = ⊤ :=
  CompleteLattice.ofProp_eq_top h
@[deprecated CompleteLattice.ofProp_meet_ofProp (since := "2026-09-24")]
theorem ofProp_and {φ₁ φ₂ : Prop} : (⌜φ₁⌝ : l) ⊓ ⌜φ₂⌝ = ⌜φ₁ ∧ φ₂⌝ :=
  CompleteLattice.ofProp_meet_ofProp
@[deprecated CompleteLattice.ofProp_join_ofProp (since := "2026-09-24")]
theorem ofProp_or {φ₁ φ₂ : Prop} : (⌜φ₁⌝ : l) ⊔ ⌜φ₂⌝ = ⌜φ₁ ∨ φ₂⌝ :=
  CompleteLattice.ofProp_join_ofProp
@[deprecated CompleteLattice.ofProp_forall_le (since := "2026-09-24")]
theorem ofProp_forall_le {β} {Φ : β → Prop} : (⌜∀ x, Φ x⌝ : l) ⊑ iInf (fun x => ⌜Φ x⌝) :=
  CompleteLattice.ofProp_forall_le
@[deprecated CompleteLattice.iSup_ofProp (since := "2026-09-24")]
theorem ofProp_exists {β} {Φ : β → Prop} :
    iSup (fun x => (⌜Φ x⌝ : l)) = ⌜∃ x, Φ x⌝ :=
  CompleteLattice.iSup_ofProp
@[deprecated CompleteLattice.iInf_ofProp (since := "2026-09-24")]
theorem ofProp_forall {β} {Φ : β → Prop} :
    iInf (fun x => (⌜Φ x⌝ : l)) = ⌜∀ x, Φ x⌝ :=
  CompleteLattice.iInf_ofProp

end Lemmas

/-- Frame a single state coordinate: from the function-order premise `(fun u => ⌜u = s⌝ ⊓ pre) ⊑ Q`
conclude the point entailment `pre ⊑ Q s`. Instantiating the premise at `u := s` collapses
`⌜s = s⌝ ⊓ pre` to `pre`. Iterating it over a state chain point-frames `pre ⊑ Q s₁ … sₙ` to the
function-order goal `(fun u⃗ => ⌜u⃗ = s⃗⌝ ⊓ pre) ⊑ Q`. -/
theorem le_apply_of_point_meet_le {σ : Type u} {β : Type v} [CompleteLattice β]
    (s : σ) (pre : β) (Q : σ → β) (h : (fun u => ⌜u = s⌝ ⊓ pre) ⊑ Q) : pre ⊑ Q s :=
  (CompleteLattice.ofProp_meet_le_eq_imp (s = s) pre (Q s)).mp (h s) rfl

end Lean.Order

end -- public section
