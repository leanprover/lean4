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

section PProd

variable {β : Type v} [CompleteLattice β]

private theorem pprod_le {p q : α ×' β} (h₁ : p.1 ⊑ q.1) (h₂ : p.2 ⊑ q.2) : p ⊑ q := by
  exact ⟨h₁, h₂⟩

/-- `mk` of the componentwise meets is the meet on a product. -/
theorem PProd.mk_meet (p q : α ×' β) : (⟨p.1 ⊓ q.1, p.2 ⊓ q.2⟩ : α ×' β) = p ⊓ q :=
  PartialOrder.rel_antisymm
    (le_meet _ _ _ (pprod_le (meet_le_left _ _) (meet_le_left _ _))
      (pprod_le (meet_le_right _ _) (meet_le_right _ _)))
    (pprod_le (le_meet _ _ _ (meet_le_left p q).1 (meet_le_right p q).1)
      (le_meet _ _ _ (meet_le_left p q).2 (meet_le_right p q).2))

/-- `mk` of the componentwise least upper bounds is the least upper bound on a product. -/
theorem PProd.mk_sup (c : α ×' β → Prop) :
    (⟨CompleteLattice.sup fun a => ∃ b, c ⟨a, b⟩,
      CompleteLattice.sup fun b => ∃ a, c ⟨a, b⟩⟩ : α ×' β) = CompleteLattice.sup c :=
  PartialOrder.rel_antisymm
    (pprod_le (sup_le _ fun _ ⟨_, hc⟩ => (le_sup c hc).1)
      (sup_le _ fun _ ⟨_, hc⟩ => (le_sup c hc).2))
    (sup_le c fun y hy => pprod_le (le_sup _ ⟨y.2, hy⟩) (le_sup _ ⟨y.1, hy⟩))

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

omit [CompleteLattice α] [CompleteLattice β] in
/-- Two pairs with equal components are equal. -/
private theorem prod_eq_of_pprod_eq {p q : α × β}
    (h : (⟨p.fst, p.snd⟩ : α ×' β) = ⟨q.fst, q.snd⟩) : p = q := by
  cases p; cases q; cases h; rfl

/-- The components of a meet are the meet of the components on `α ×' β`. -/
private theorem prod_meet_toPProd (p q : α × β) :
    (⟨(p ⊓ q).fst, (p ⊓ q).snd⟩ : α ×' β) = ⟨p.fst, p.snd⟩ ⊓ ⟨q.fst, q.snd⟩ := by
  refine PartialOrder.rel_antisymm (le_meet _ _ _ (meet_le_left p q) (meet_le_right p q)) ?_
  let r : α × β := ((⟨p.fst, p.snd⟩ ⊓ ⟨q.fst, q.snd⟩ : α ×' β).fst,
                    (⟨p.fst, p.snd⟩ ⊓ ⟨q.fst, q.snd⟩ : α ×' β).snd)
  exact le_meet r p q (meet_le_left (⟨p.fst, p.snd⟩ : α ×' β) ⟨q.fst, q.snd⟩)
    (meet_le_right (⟨p.fst, p.snd⟩ : α ×' β) ⟨q.fst, q.snd⟩)

/-- The components of a least upper bound are the least upper bound of the components on
`α ×' β`. -/
private theorem prod_sup_toPProd (c : α × β → Prop) :
    (⟨(CompleteLattice.sup c).fst, (CompleteLattice.sup c).snd⟩ : α ×' β)
      = CompleteLattice.sup fun x => c (x.fst, x.snd) :=
  is_sup_unique
    (fun x => Iff.trans (CompleteLattice.sup_spec c (x.fst, x.snd))
      ⟨fun h y hy => h (y.fst, y.snd) hy, fun h y hy => h ⟨y.fst, y.snd⟩ hy⟩)
    (CompleteLattice.sup_spec _)

/-- `mk` of the componentwise meets is the meet on a product. -/
theorem Prod.mk_meet (p q : α × β) : ((p.fst ⊓ q.fst, p.snd ⊓ q.snd) : α × β) = p ⊓ q :=
  prod_eq_of_pprod_eq <| by rw [prod_meet_toPProd, ← PProd.mk_meet]

/-- The first component of a meet is the meet of the first components. -/
@[simp] theorem Prod.fst_meet (p q : α × β) : (p ⊓ q).fst = p.fst ⊓ q.fst := by
  rw [← Prod.mk_meet]

/-- The second component of a meet is the meet of the second components. -/
@[simp] theorem Prod.snd_meet (p q : α × β) : (p ⊓ q).snd = p.snd ⊓ q.snd := by
  rw [← Prod.mk_meet]

/-- The first component of the bottom element is the bottom element. Propositional (not
definitional), because `⊥` is `csup ∅`, not a constructor application. -/
theorem Prod.fst_bot {α : Type u} {β : Type v} [CCPO α] [CCPO β] :
    (⊥ : α × β).fst = (⊥ : α) :=
  PartialOrder.rel_antisymm (bot_le ((⊥ : α), (⊥ : β))).left (bot_le _)

/-- The second component of the bottom element is the bottom element. Propositional (not
definitional), because `⊥` is `csup ∅`, not a constructor application. -/
theorem Prod.snd_bot {α : Type u} {β : Type v} [CCPO α] [CCPO β] :
    (⊥ : α × β).snd = (⊥ : β) :=
  PartialOrder.rel_antisymm (bot_le ((⊥ : α), (⊥ : β))).right (bot_le _)

/-- The first component of the top element is the top element. Propositional (not
definitional), because `⊤` is a supremum, not a constructor application. -/
theorem Prod.fst_top : (⊤ : α × β).fst = (⊤ : α) :=
  PartialOrder.rel_antisymm (le_top _) (le_top ((⊤ : α), (⊤ : β))).left

/-- The second component of the top element is the top element. Propositional (not
definitional), because `⊤` is a supremum, not a constructor application. -/
theorem Prod.snd_top : (⊤ : α × β).snd = (⊤ : β) :=
  PartialOrder.rel_antisymm (le_top _) (le_top ((⊤ : α), (⊤ : β))).right

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
