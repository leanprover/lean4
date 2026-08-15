/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Std.Internal.Order.Lemmas

@[expose] public section

/-!
# Supremum-preserving maps and their upper adjoints

A supremum-preserving map on a complete lattice is a lower adjoint. Its upper adjoint is the
implication belonging to it: Heyting `⇨` for the lattice meet, a magic wand for a separating
conjunction.
-/

namespace Lean.Order

open Std.Internal.Order

universe u v w

variable {α : Type u} [CompleteLattice α]

/--
`f : α → α` *preserves suprema* if it distributes over arbitrary suprema:
`f (sup s) = sup { f x | x ∈ s }`. Equivalently `f` is a lower adjoint, so it has an upper adjoint
`PreservesSup.upperAdjoint f`.

A frame operator acts by a supremum-preserving map for each resource `r`: the lattice meet
`(a ⊓ ·)`,
or a cost combinator `(costConj r)` for a counter resource. The upper adjoint is the corresponding
implication: Heyting `⇨` for the meet, a magic wand for separating conjunction.
-/
class PreservesSup {α : Type u} [CompleteLattice α] (f : α → α) : Prop where
  /-- `f` preserves joins. -/
  map_sup (s : α → Prop) :
    f (CompleteLattice.sup s) = CompleteLattice.sup (fun y => ∃ x, s x ∧ y = f x)

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

namespace PreservesSup

/-- The upper adjoint of `f`: the join of all `x` with `f x ⊑ b`. For `f = (a ⊓ ·)` this is Heyting
implication `a ⇨ ·`. -/
noncomputable def upperAdjoint (f : α → α) (b : α) : α := CompleteLattice.sup (fun x => f x ⊑ b)

/-- `upperAdjoint f b` is the least upper bound of `{x | f x ⊑ b}` by definition. -/
theorem upperAdjoint_spec (f : α → α) (b : α) : is_sup (fun x : α => f x ⊑ b) (upperAdjoint f b) :=
  CompleteLattice.sup_spec (fun x : α => f x ⊑ b)

/-- Unit, free from the definition of `upperAdjoint`: `f x ⊑ b → x ⊑ upperAdjoint f b`. Needs only
`CompleteLattice`. -/
theorem le_upperAdjoint (f : α → α) {b x : α} (h : f x ⊑ b) : x ⊑ upperAdjoint f b :=
  le_sup (c := fun x : α => f x ⊑ b) h

/-- Counit (modus ponens), from supremum preservation: `f (upperAdjoint f b) ⊑ b`. -/
theorem upperAdjoint_le (f : α → α) [PreservesSup f] (b : α) : f (upperAdjoint f b) ⊑ b := by
  unfold upperAdjoint
  rw [PreservesSup.map_sup (f := f)]
  apply sup_le
  rintro y ⟨x, hx, rfl⟩
  exact hx

/-- Monotonicity of a supremum-preserving `f`, derived from supremum preservation. -/
theorem map_mono (f : α → α) [PreservesSup f] {b b' : α} (h : b ⊑ b') : f b ⊑ f b' := by
  have hsup : (CompleteLattice.sup (fun y => y ⊑ b')) = b' :=
    is_sup_unique (CompleteLattice.sup_spec _)
      (fun x => ⟨fun hb' y hy => PartialOrder.rel_trans hy hb',
                 fun hy => hy b' PartialOrder.rel_refl⟩)
  calc f b ⊑ f (CompleteLattice.sup (fun y => y ⊑ b')) := by
            rw [PreservesSup.map_sup (f := f)]; exact le_sup _ ⟨b, h, rfl⟩
    _ = f b' := by rw [hsup]

/-- A right adjoint is monotone. -/
theorem upperAdjoint_mono (f : α → α) [PreservesSup f] {b b' : α} (h : b ⊑ b') :
    upperAdjoint f b ⊑ upperAdjoint f b' :=
  le_upperAdjoint f (PartialOrder.rel_trans (upperAdjoint_le f b) h)

end PreservesSup

/-- Frame elimination: a join on the left of a meet is eliminated pointwise. -/
theorem iSup_meet_le {ι : Type v} {P R : α} {Φ : ι → α} [PreservesSup (meet P)]
    (h : ∀ i, Φ i ⊓ P ⊑ R) : iSup Φ ⊓ P ⊑ R := by
  refine PartialOrder.rel_trans
    (le_meet _ _ _ (meet_le_right _ _) (meet_le_left _ _)) ?_
  show meet P (iSup Φ) ⊑ R
  unfold iSup
  rw [PreservesSup.map_sup (f := meet P)]
  apply sup_le
  rintro y ⟨x, ⟨i, rfl⟩, rfl⟩
  exact PartialOrder.rel_trans
    (le_meet _ _ _ (meet_le_right _ _) (meet_le_left _ _)) (h i)

end Lean.Order

end -- public section
