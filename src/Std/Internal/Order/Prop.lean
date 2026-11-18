/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Gladshtein, Sebastian Graf
-/
module

prelude
public import Std.Internal.Order.Lemmas
public import Init.ByCases
import Init.Classical

@[expose] public section

/-!
# The lattice of propositions

Lemmas at carrier `Prop`: `⊑` is implication, `⊓` is `∧`, `⊔` is `∨`, `⨅` is `∀`, `⨆` is `∃`, `⊤` is
`True`, `⊥` is `False`, `⇨` is `→`, and `⌜p⌝` is `p`.
-/

namespace Lean.Order

open PartialOrder Std.Internal.Order

universe uₗ

theorem le_prop_eq_imp (p q : Prop) : (p ⊑ q) = (p → q) := rfl

theorem le_of_imp_top_le (x y : Prop) : (x → (⊤ : Prop) ⊑ y) → x ⊑ y :=
  fun h hx => h hx (le_top True trivial)

theorem top_le_prop (x : Prop) : x → (⊤ : Prop) ⊑ x :=
  fun hx _ => hx

theorem le_prop_of_right (x y : Prop) : y → x ⊑ y :=
  fun hy _ => hy

theorem of_top_le_prop {x : Prop} : (⊤ : Prop) ⊑ x → x :=
  fun h => h (le_top True trivial)

theorem true_le_of_top_le (x : Prop) : ((⊤ : Prop) ⊑ x) → (True : Prop) ⊑ x :=
  fun h => le_prop_of_right True x (of_top_le_prop h)

theorem iInf_prop_eq_forall {ι : Type uₗ} (f : ι → Prop) :
    (iInf f : Prop) = (∀ i, f i) := by
  apply propext
  constructor
  · intro hf i
    exact (iInf_le f i) hf
  · intro hall
    exact (le_iInf f (x := ∀ i, f i) (fun i h => h i)) hall

/-- Introduction rule for a `∀` on the RHS of a `Prop` entailment. -/
theorem le_forall {β : Sort uₗ} (p : Prop) (q : β → Prop)
    (h : ∀ x, p ⊑ q x) : p ⊑ (∀ x, q x) :=
  fun hp x => h x hp

theorem le_and (p a b : Prop) (ha : p ⊑ a) (hb : p ⊑ b) : p ⊑ (a ∧ b) :=
  fun hp => ⟨ha hp, hb hp⟩

theorem le_exists_prop (p a : Prop) (b : a → Prop) (ha : p ⊑ a) (hb : ∀ h : a, p ⊑ b h) :
    p ⊑ (∃ h : a, b h) :=
  fun hp => ⟨ha hp, hb (ha hp) hp⟩

theorem iSup_prop_eq_exists {ι : Type uₗ} (f : ι → Prop) :
    (iSup f : Prop) = (∃ i, f i) := by
  apply propext
  constructor
  · intro hsup
    exact (iSup_le f (x := ∃ i, f i) (fun i hi => ⟨i, hi⟩)) hsup
  · intro ⟨i, hi⟩
    exact (le_iSup f i) hi

theorem meet_prop_eq_and (a b : Prop) : (a ⊓ b : Prop) = (a ∧ b) := by
  apply propext
  constructor
  · intro hab
    exact ⟨(meet_le_left a b) hab, (meet_le_right a b) hab⟩
  · intro hab
    exact (le_meet (a ∧ b) a b (fun h => h.left) (fun h => h.right)) hab

theorem join_prop_eq_or (a b : Prop) : (a ⊔ b : Prop) = (a ∨ b) := by
  apply propext
  constructor
  · intro hab
    exact (join_le a b (a ∨ b) (fun ha => Or.inl ha) (fun hb => Or.inr hb)) hab
  · intro hab
    cases hab with
    | inl ha => exact (left_le_join a b) ha
    | inr hb => exact (right_le_join a b) hb

/-- The top element of the `Prop` lattice is `True`. -/
theorem top_prop_eq : (⊤ : Prop) = True :=
  propext ⟨fun _ => trivial, fun _ => le_top True trivial⟩

/-- The bottom element of the `Prop` lattice is `False`. -/
theorem bot_prop_eq : (⊥ : Prop) = False :=
  propext ⟨fun h => bot_le False h, fun h => h.elim⟩

@[deprecated le_prop_of_right (since := "2026-09-24")]
theorem le_of_right (x y : Prop) : y → x ⊑ y := le_prop_of_right x y

/-- Embedding a proposition into the `Prop` lattice (`⌜p⌝`) is the proposition itself. -/
theorem CompleteLattice.ofProp_prop_eq (p : Prop) : (⌜p⌝ : Prop) = p := by
  simp only [CompleteLattice.ofProp]
  rcases Classical.em p with hp | hp <;> simp [hp, top_prop_eq, bot_prop_eq]

@[deprecated CompleteLattice.ofProp_prop_eq (since := "2026-09-24")]
theorem ofProp_prop_eq (p : Prop) : (⌜p⌝ : Prop) = p :=
  CompleteLattice.ofProp_prop_eq p

theorem himp_prop_eq_imp (a b : Prop) : ((a ⇨ b : Prop) = (a → b)) := by
  apply propext
  constructor
  · intro hab
    have hs : (a ⇨ b : Prop) ⊑ (a → b) := by
      unfold himp PreservesSup.upperAdjoint
      apply sup_le
      intro x hx hxTrue haTrue
      have hax : a ⊓ x := by
        simpa [meet_prop_eq_and] using (And.intro haTrue hxTrue)
      exact hx hax
    exact hs hab
  · intro hab
    have hx : a ⊓ (a → b) ⊑ b := by
      intro hax
      have hax' : a ∧ (a → b) := by
        simpa [meet_prop_eq_and] using hax
      exact hax'.right hax'.left
    exact (PreservesSup.le_upperAdjoint (meet a) (b := b) (x := (a → b)) hx) hab

end Lean.Order

end -- public section
