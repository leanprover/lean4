/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Std.Internal.Order.Product
import all Std.Internal.Order.Product

@[expose] public section

/-!
# Supremum-preserving maps and their upper adjoints

The supremum-preserving maps of the lattice theory (the identity, pointwise lifts, the lattice meet
on `Prop`, functions, pairs, `PProd` and `Unit`, and `Prod.map`), and the laws of their upper
adjoints.
-/

namespace Lean.Order

open Std.Internal.Order

universe u v w

variable {α : Type u} [CompleteLattice α]
instance : PreservesSup (id : α → α) where
  map_sup s := by
    show CompleteLattice.sup s = _
    congr 1
    funext y
    exact propext ⟨fun hy => ⟨y, hy, rfl⟩, fun ⟨x, hx, hxy⟩ => hxy ▸ hx⟩

instance {ε : Type v} (f : α → α) [PreservesSup f] :
    PreservesSup (Function.comp f : (ε → α) → ε → α) where
  map_sup s := by
    funext e
    show f (CompleteLattice.sup s e) = _
    rw [sup_apply, sup_apply, PreservesSup.map_sup (f := f)]
    congr 1
    funext v
    apply propext
    constructor
    · rintro ⟨w, ⟨g, hg, rfl⟩, rfl⟩
      exact ⟨f ∘ g, ⟨g, hg, rfl⟩, rfl⟩
    · rintro ⟨g, ⟨g', hg', rfl⟩, rfl⟩
      exact ⟨g' e, ⟨g', hg', rfl⟩, rfl⟩

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

section PProd

variable {β : Type v} [CompleteLattice β]
private theorem fst_meet (p q : α ×' β) : (p ⊓ q).1 = p.1 ⊓ q.1 := by rw [← PProd.mk_meet]
private theorem snd_meet (p q : α ×' β) : (p ⊓ q).2 = p.2 ⊓ q.2 := by rw [← PProd.mk_meet]

private theorem fst_sup (c : α ×' β → Prop) :
    (CompleteLattice.sup c).1 = CompleteLattice.sup fun a => ∃ b, c ⟨a, b⟩ := by
  rw [← PProd.mk_sup]

private theorem snd_sup (c : α ×' β → Prop) :
    (CompleteLattice.sup c).2 = CompleteLattice.sup fun b => ∃ a, c ⟨a, b⟩ := by
  rw [← PProd.mk_sup]

/-- A product lattice preserves suprema componentwise: meets, least upper bounds and the order all
act on the two components separately. -/
instance [∀ a : α, PreservesSup (meet a)] [∀ b : β, PreservesSup (meet b)] (p : α ×' β) :
    PreservesSup (meet p) where
  map_sup s := by
    refine PartialOrder.rel_antisymm (pprod_le ?_ ?_)
      (sup_le _ fun _ ⟨x, hx, hy⟩ => hy ▸ meet_mono PartialOrder.rel_refl (le_sup s hx))
    · simp only [fst_meet, fst_sup]
      rw [PreservesSup.map_sup (f := meet p.1)]
      refine sup_le _ ?_
      rintro _ ⟨a, ⟨b, hs⟩, rfl⟩
      exact le_sup _ ⟨p.2 ⊓ b, ⟨a, b⟩, hs, PProd.mk_meet p ⟨a, b⟩⟩
    · simp only [snd_meet, snd_sup]
      rw [PreservesSup.map_sup (f := meet p.2)]
      refine sup_le _ ?_
      rintro _ ⟨b, ⟨a, hs⟩, rfl⟩
      exact le_sup _ ⟨p.1 ⊓ a, ⟨a, b⟩, hs, PProd.mk_meet p ⟨a, b⟩⟩

end PProd

section Prod

variable {β : Type v} [CompleteLattice β]
/-- The order on `α × β` is the order on `α ×' β` at the two components. -/
private theorem prod_le_iff (p q : α × β) :
    p ⊑ q ↔ (⟨p.fst, p.snd⟩ : α ×' β) ⊑ ⟨q.fst, q.snd⟩ := Iff.rfl

instance (f : α → α) (g : β → β) [PreservesSup f] [PreservesSup g] :
    PreservesSup (Prod.map f g) where
  map_sup s := by
    show (f (CompleteLattice.sup s).1, g (CompleteLattice.sup s).2) = _
    refine Eq.trans ?_ (Prod.mk_sup _)
    congr 1
    · rw [Prod.fst_sup, PreservesSup.map_sup (f := f)]
      congr 1
      funext y
      apply propext
      constructor
      · rintro ⟨w, ⟨b, hs⟩, rfl⟩
        exact ⟨g b, (w, b), hs, rfl⟩
      · rintro ⟨b, x, hx, heq⟩
        obtain ⟨h1, h2⟩ := Prod.mk.inj heq
        exact ⟨x.1, ⟨x.2, hx⟩, h1⟩
    · rw [Prod.snd_sup, PreservesSup.map_sup (f := g)]
      congr 1
      funext y
      apply propext
      constructor
      · rintro ⟨w, ⟨a, hs⟩, rfl⟩
        exact ⟨f a, (a, w), hs, rfl⟩
      · rintro ⟨a, x, hx, heq⟩
        obtain ⟨h1, h2⟩ := Prod.mk.inj heq
        exact ⟨x.2, ⟨x.1, hx⟩, h2⟩

/-- A product lattice preserves suprema at the two components. -/
instance [∀ a : α, PreservesSup (meet a)] [∀ b : β, PreservesSup (meet b)] (p : α × β) :
    PreservesSup (meet p) where
  map_sup s := by
    refine PartialOrder.rel_antisymm ?_
      (sup_le _ fun _ ⟨x, hx, hy⟩ => hy ▸ meet_mono PartialOrder.rel_refl (le_sup s hx))
    rw [prod_le_iff, prod_meet_toPProd, prod_sup_toPProd, prod_sup_toPProd,
      PreservesSup.map_sup (f := meet (⟨p.fst, p.snd⟩ : α ×' β))]
    refine sup_le _ ?_
    rintro _ ⟨x, hx, rfl⟩
    exact le_sup _
      ⟨(x.fst, x.snd), hx, prod_eq_of_pprod_eq (prod_meet_toPProd p (x.fst, x.snd)).symm⟩

end Prod

/-- `Unit` carries a single value, so every map on it preserves suprema. -/
instance (a : Unit) : PreservesSup (meet a) where
  map_sup _ := Subsingleton.elim _ _

namespace PreservesSup

/-- `upperAdjoint f b` is the least upper bound of `{x | f x ⊑ b}` by definition. -/
theorem upperAdjoint_spec (f : α → α) (b : α) : is_sup (fun x : α => f x ⊑ b) (upperAdjoint f b) :=
  CompleteLattice.sup_spec (fun x : α => f x ⊑ b)

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

theorem upperAdjoint_id (b : α) : upperAdjoint (id : α → α) b = b := by
  apply PartialOrder.rel_antisymm
  · unfold upperAdjoint
    exact sup_le _ fun x hx => hx
  · exact le_upperAdjoint _ PartialOrder.rel_refl

theorem upperAdjoint_comp_apply {ε : Type v} (f : α → α) [PreservesSup f] (X : ε → α) (e : ε) :
    upperAdjoint (Function.comp f) X e = upperAdjoint f (X e) := by
  apply PartialOrder.rel_antisymm
  · show upperAdjoint (Function.comp f) X e ⊑ _
    unfold upperAdjoint
    rw [sup_apply]
    apply sup_le
    rintro y ⟨Y, hY, rfl⟩
    exact le_upperAdjoint f (hY e)
  · have h : (fun e' => upperAdjoint f (X e')) ⊑ upperAdjoint (Function.comp f) X :=
      le_upperAdjoint _ fun e' => upperAdjoint_le f (X e')
    exact h e

theorem upperAdjoint_prodMap_fst {β : Type v} [CompleteLattice β]
    (f : α → α) (g : β → β) [PreservesSup f] [PreservesSup g] (E : α × β) :
    (upperAdjoint (Prod.map f g) E).fst = upperAdjoint f E.fst := by
  apply PartialOrder.rel_antisymm
  · show (upperAdjoint (Prod.map f g) E).fst ⊑ _
    unfold upperAdjoint
    rw [Prod.fst_sup]
    apply sup_le
    rintro a ⟨b, hab⟩
    exact le_upperAdjoint f hab.left
  · have h : ((upperAdjoint f E.fst, upperAdjoint g E.snd) : α × β)
        ⊑ upperAdjoint (Prod.map f g) E :=
      le_upperAdjoint _ (x := (upperAdjoint f E.fst, upperAdjoint g E.snd))
        (Prod.mk_le _ _ _ (upperAdjoint_le f E.fst) (upperAdjoint_le g E.snd))
    exact h.left

theorem upperAdjoint_prodMap_snd {β : Type v} [CompleteLattice β]
    (f : α → α) (g : β → β) [PreservesSup f] [PreservesSup g] (E : α × β) :
    (upperAdjoint (Prod.map f g) E).snd = upperAdjoint g E.snd := by
  apply PartialOrder.rel_antisymm
  · show (upperAdjoint (Prod.map f g) E).snd ⊑ _
    unfold upperAdjoint
    rw [Prod.snd_sup]
    apply sup_le
    rintro b ⟨a, hab⟩
    exact le_upperAdjoint g hab.right
  · have h : ((upperAdjoint f E.fst, upperAdjoint g E.snd) : α × β)
        ⊑ upperAdjoint (Prod.map f g) E :=
      le_upperAdjoint _ (x := (upperAdjoint f E.fst, upperAdjoint g E.snd))
        (Prod.mk_le _ _ _ (upperAdjoint_le f E.fst) (upperAdjoint_le g E.snd))
    exact h.right

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
