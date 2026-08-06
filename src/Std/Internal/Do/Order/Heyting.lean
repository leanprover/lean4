/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Gladshtein, Sebastian Graf
-/
module

prelude
public import Std.Internal.Do.Order.PreservesSup

public section

namespace Lean.Order

universe u

variable {α : Type u} [CompleteLattice α]

instance (a : Prop) : PreservesSup (meet a) where
  map_sup s := by
    show a ⊓ CompleteLattice.sup s = CompleteLattice.sup (fun y => ∃ x, s x ∧ y = a ⊓ x)
    have sup_eq_propSup (c : Prop → Prop) : CompleteLattice.sup c = propSup c := by
      apply propext
      constructor
      · exact sup_le c (fun y hy hyTrue => ⟨y, hy, hyTrue⟩)
      · intro ⟨y, hy, hyTrue⟩
        exact le_sup (c := c) hy hyTrue
    rw [sup_eq_propSup s, sup_eq_propSup (fun y => ∃ x, s x ∧ y = a ⊓ x)]
    apply propext
    simp only [propSup, meet_prop_eq_and]
    constructor
    · rintro ⟨ha, x, hsx, hx⟩
      exact ⟨a ∧ x, ⟨x, hsx, rfl⟩, ha, hx⟩
    · rintro ⟨p, ⟨x, hsx, hp_eq⟩, hp⟩
      subst p
      exact ⟨hp.1, x, hsx, hp.2⟩

instance {σ : Type v} {β : σ → Type u} [∀ s, CompleteLattice (β s)]
    [∀ s, ∀ c : β s, PreservesSup (meet c)] (a : ∀ s, β s) : PreservesSup (meet a) where
  map_sup s := by
    show a ⊓ CompleteLattice.sup s = CompleteLattice.sup (fun y => ∃ x, s x ∧ y = a ⊓ x)
    funext t
    rw [meet_apply, sup_apply, sup_apply, PreservesSup.map_sup (f := meet (a t))]
    congr 1
    funext w
    apply propext
    constructor
    · rintro ⟨v, ⟨f, hf, hft⟩, rfl⟩
      exact ⟨a ⊓ f, ⟨f, hf, rfl⟩, by rw [meet_apply, hft]⟩
    · rintro ⟨g, ⟨x, hx, rfl⟩, hgt⟩
      exact ⟨x t, ⟨x, hx, rfl⟩, by rw [← hgt, meet_apply]⟩

/-- Heyting implication: the upper adjoint of the lattice meet. For `Prop` it is `→`. -/
@[expose] noncomputable def himp {α : Type u} [CompleteLattice α] (a b : α) : α :=
  PreservesSup.upperAdjoint (meet a) b

@[inherit_doc himp] scoped infixr:60 " ⇨ " => himp

/-- Unit for `⇨`, the meet specialization of `PreservesSup.le_upperAdjoint`: `a ⊓ x ⊑ b → x ⊑ a ⇨ b`. -/
theorem le_himp {a b x : α} (h : a ⊓ x ⊑ b) : x ⊑ a ⇨ b := by
  unfold himp; exact PreservesSup.le_upperAdjoint (meet a) h

/-- Counit for `⇨`, the meet specialization of `PreservesSup.upperAdjoint_le`: `a ⊓ (a ⇨ b) ⊑ b`. -/
theorem meet_himp_le {a b : α} [PreservesSup (meet a)] : a ⊓ (a ⇨ b) ⊑ b := by
  unfold himp; exact PreservesSup.upperAdjoint_le (meet a) b

@[simp] theorem himp_prop_eq_imp (a b : Prop) : ((a ⇨ b : Prop) = (a → b)) := by
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

/-- Pointwise characterization of Heyting implication on function lattices. -/
@[simp] theorem himp_apply
    {σ : Type v} {β : Type u} [CompleteLattice β]
    (a b : σ → β) (s : σ) :
    (a ⇨ b) s = (a s ⇨ b s) := by
  classical
  unfold himp PreservesSup.upperAdjoint
  rw [sup_apply]
  apply PartialOrder.rel_antisymm
  · apply sup_le
    intro y ⟨f, hf, hfs⟩
    rw [← hfs]
    have hsf : a s ⊓ f s ⊑ b s := by
      simpa [meet_apply] using (hf s)
    exact le_sup (c := fun z : β => a s ⊓ z ⊑ b s) hsf
  · apply sup_le
    intro y hy
    let f : σ → β := fun t => if t = s then y else ⊥
    have hf : a ⊓ f ⊑ b := by
      intro t
      simp only [meet_apply, f]
      split
      · next h => subst h; exact hy
      · exact PartialOrder.rel_trans (meet_le_right ..) (bot_le ..)
    have hs : f s = y := by simp [f]
    exact le_sup (c := fun z => ∃ g, (a ⊓ g ⊑ b) ∧ g s = z) ⟨f, hf, hs⟩

end Lean.Order

end -- public section
