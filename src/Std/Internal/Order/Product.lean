/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Gladshtein, Sebastian Graf
-/
module

prelude
public import Std.Internal.Order.Prop
public import Init.ByCases
import Init.Classical
import Init.TacticsExtra

@[expose] public section

/-!
# Projections of lattice operations

The lattice operations on functions, pairs and `PProd` are pointwise and componentwise: applying a
function or projecting a component commutes with `⊤`, `⊥`, `⊓`, `⊔`, `⨅`, `⨆`, `⌜·⌝` and `⇨`, and
`⊑` on functions and pairs is pointwise and componentwise.
-/

namespace Lean.Order

open PartialOrder Std.Internal.Order

universe u v w uₗ vₗ wₗ

/-! ## Functions -/

section Functions

/-- Pointwise characterization of indexed infimum on function lattices. -/
theorem iInf_apply
    {ι : Type vₗ} {σ : Type wₗ} {β : Type uₗ} [CompleteLattice β]
    (f : ι → σ → β) (s : σ) :
    (iInf f) s = iInf (fun i => f i s) := by
  apply PartialOrder.rel_antisymm
  ·
    apply le_iInf
    intro i
    exact (iInf_le f i) s
  ·
    let g : σ → β := fun t => iInf (fun i => f i t)
    have hg : g ⊑ iInf f := by
      apply le_iInf
      intro i t
      exact iInf_le (fun j => f j t) i
    simpa [g] using hg s

/-- Pointwise characterization of indexed supremum on function lattices. -/
theorem iSup_apply
    {ι : Type vₗ} {σ : Type wₗ} {β : Type uₗ} [CompleteLattice β]
    (f : ι → σ → β) (s : σ) :
    (iSup f) s = iSup (fun i => f i s) := by
  apply PartialOrder.rel_antisymm
  · let g : σ → β := fun t => iSup (fun i => f i t)
    have hg : iSup f ⊑ g := by
      apply iSup_le
      intro i t
      exact le_iSup (fun j => f j t) i
    exact hg s
  · apply iSup_le
    intro i
    exact (le_iSup f i) s

/-- Pointwise characterization of `CompleteLattice.sup` on function lattices:
`(sup c) s = sup (fun y => ∃ f, c f ∧ f s = y)`. -/
theorem sup_apply
    {σ : Type vₗ} {β : σ → Type wₗ} [∀ s, CompleteLattice (β s)]
    (c : (∀ s, β s) → Prop) (s : σ) :
    CompleteLattice.sup c s = CompleteLattice.sup (fun y => ∃ f, c f ∧ f s = y) := by
  apply PartialOrder.rel_antisymm
  · -- sup c s ⊑ sup {y | ∃ f ∈ c, f s = y}
    let g : ∀ t, β t := fun t => CompleteLattice.sup (fun y => ∃ f, c f ∧ f t = y)
    have hg : CompleteLattice.sup c ⊑ g := by
      apply sup_le
      intro f hf t
      apply le_sup
      exact ⟨f, hf, rfl⟩
    exact hg s
  · -- sup {y | ∃ f ∈ c, f s = y} ⊑ sup c s
    apply sup_le
    intro y ⟨f, hf, hfs⟩
    rw [← hfs]
    exact (le_sup (c := c) hf) s

/-- Pointwise characterization of binary meet on function lattices. -/
theorem meet_apply
    {σ : Type vₗ} {β : σ → Type wₗ} [∀ s, CompleteLattice (β s)]
    (a b : ∀ s, β s) (s : σ) :
    (a ⊓ b) s = a s ⊓ b s := by
  apply PartialOrder.rel_antisymm
  · apply le_meet
    · exact (meet_le_left a b) s
    · exact (meet_le_right a b) s
  · classical
    let f : ∀ t, β t := fun t => if t = s then a t ⊓ b t else ⊥
    have hf_left : f ⊑ a := by
      intro t
      simp only [f]
      split
      · next h => subst h; exact meet_le_left ..
      · exact bot_le _
    have hf_right : f ⊑ b := by
      intro t
      simp only [f]
      split
      · next h => subst h; exact meet_le_right ..
      · exact bot_le _
    have hf_meet : f ⊑ a ⊓ b := le_meet f a b hf_left hf_right
    have hs : f s = a s ⊓ b s := by simp [f]
    exact hs ▸ hf_meet s

/-- Pointwise characterization of binary join on function lattices. -/
theorem join_apply
    {σ : Type vₗ} {β : Type wₗ} [CompleteLattice β]
    (a b : σ → β) (s : σ) :
    (a ⊔ b) s = a s ⊔ b s := by
  apply PartialOrder.rel_antisymm
  ·
    have hfun : a ⊔ b ⊑ fun t => a t ⊔ b t :=
      join_le a b (fun t => a t ⊔ b t)
        (fun t => left_le_join (a t) (b t))
        (fun t => right_le_join (a t) (b t))
    exact hfun s
  ·
    apply join_le
    · exact (left_le_join a b) s
    · exact (right_le_join a b) s

/-- Pointwise characterization of `⊤` on a function lattice. -/
theorem top_apply {σ : Type vₗ} {β : Type wₗ} [CompleteLattice β] (s : σ) :
    (⊤ : σ → β) s = (⊤ : β) :=
  PartialOrder.rel_antisymm (le_top _) ((le_top (fun _ : σ => (⊤ : β))) s)

/-- Pointwise characterization of `⊥` on a function lattice. -/
theorem bot_apply {σ : Type vₗ} {β : Type wₗ} [CCPO β] (s : σ) :
    (⊥ : σ → β) s = (⊥ : β) :=
  PartialOrder.rel_antisymm ((bot_le (fun _ : σ => (⊥ : β))) s) (bot_le _)

/-- Entailment on a function lattice is pointwise. -/
theorem le_pi_eq_forall {σ : Type vₗ} {β : σ → Type wₗ} [∀ s, PartialOrder (β s)]
    (a b : ∀ s, β s) : (a ⊑ b) = ∀ s, a s ⊑ b s := rfl

/-- Entailment on a pair lattice is componentwise. -/
theorem le_prod_eq_and {α : Type vₗ} {β : Type wₗ} [PartialOrder α] [PartialOrder β]
    (a b : α × β) : (a ⊑ b) = (a.1 ⊑ b.1 ∧ a.2 ⊑ b.2) := rfl

/-- Entailment between functions follows from pointwise entailment. -/
theorem le_of_forall_le {σ : Type uₗ} {β : Type vₗ} [PartialOrder β] {f g : σ → β} :
    (∀ s, f s ⊑ g s) → f ⊑ g := Eq.mpr (le_pi_eq_forall f g)

/-- `⊤ ⊑ g` for a function `g` follows from pointwise `⊤ ⊑ g s`. -/
theorem top_le_of_forall_top_le {σ : Type uₗ} {β : Type vₗ} [CompleteLattice β] {g : σ → β} :
    (∀ s, (⊤ : β) ⊑ g s) → (⊤ : σ → β) ⊑ g := by
  intro h s
  rw [top_apply]
  exact h s

@[deprecated le_pi_eq_forall +typeChanged (since := "2026-09-24")]
theorem le_iff_forall_le {σ : Type uₗ} {β : Type vₗ} [PartialOrder β] {f g : σ → β} :
    (f ⊑ g) ↔ (∀ s, f s ⊑ g s) := Iff.rfl

section

variable {l : Type uₗ} [CompleteLattice l]

@[deprecated le_pi_eq_forall +typeChanged (since := "2026-09-24")]
theorem le_iff_forall_le_1 {σ : Type vₗ} {P Q : σ → l} :
    P ⊑ Q ↔ ∀ s, P s ⊑ Q s := Iff.rfl
@[deprecated le_pi_eq_forall +typeChanged (since := "2026-09-24")]
theorem le_iff_forall_le_2 {σ₁ σ₂ : Type vₗ} {P Q : σ₁ → σ₂ → l} :
    P ⊑ Q ↔ ∀ s₁ s₂, P s₁ s₂ ⊑ Q s₁ s₂ := Iff.rfl
@[deprecated le_pi_eq_forall +typeChanged (since := "2026-09-24")]
theorem le_iff_forall_le_3 {σ₁ σ₂ σ₃ : Type vₗ} {P Q : σ₁ → σ₂ → σ₃ → l} :
    P ⊑ Q ↔ ∀ s₁ s₂ s₃, P s₁ s₂ s₃ ⊑ Q s₁ s₂ s₃ := Iff.rfl
@[deprecated le_pi_eq_forall +typeChanged (since := "2026-09-24")]
theorem le_iff_forall_le_4 {σ₁ σ₂ σ₃ σ₄ : Type vₗ} {P Q : σ₁ → σ₂ → σ₃ → σ₄ → l} :
    P ⊑ Q ↔ ∀ s₁ s₂ s₃ s₄, P s₁ s₂ s₃ s₄ ⊑ Q s₁ s₂ s₃ s₄ := Iff.rfl
@[deprecated le_pi_eq_forall +typeChanged (since := "2026-09-24")]
theorem le_iff_forall_le_5 {σ₁ σ₂ σ₃ σ₄ σ₅ : Type vₗ} {P Q : σ₁ → σ₂ → σ₃ → σ₄ → σ₅ → l} :
    P ⊑ Q ↔ ∀ s₁ s₂ s₃ s₄ s₅, P s₁ s₂ s₃ s₄ s₅ ⊑ Q s₁ s₂ s₃ s₄ s₅ := Iff.rfl

end

/-- Pointwise characterization of `CompleteLattice.ofProp` on a function lattice. -/
theorem CompleteLattice.ofProp_apply
    {σ : Type v} {β : Type u} [CompleteLattice β] (p : Prop) (s : σ) :
    (⌜p⌝ : σ → β) s = (⌜p⌝ : β) := by
  simp only [CompleteLattice.ofProp]
  rcases Classical.em p with h | h <;> simp [h, top_apply, bot_apply]

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

/-- Pointwise characterization of Heyting implication on function lattices. -/
theorem himp_apply
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

end Functions

/-! ## `PProd` -/

section PProd

variable {α : Type u} [CompleteLattice α] {β : Type v} [CompleteLattice β]

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

end PProd

/-! ## Pairs -/

section Prod

variable {α : Type u} [CompleteLattice α] {β : Type v} [CompleteLattice β]

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
theorem Prod.fst_meet (p q : α × β) : (p ⊓ q).fst = p.fst ⊓ q.fst := by
  rw [← Prod.mk_meet]

/-- The second component of a meet is the meet of the second components. -/
theorem Prod.snd_meet (p q : α × β) : (p ⊓ q).snd = p.snd ⊓ q.snd := by
  rw [← Prod.mk_meet]

theorem Prod.fst_join (p q : α × β) : (p ⊔ q).fst = p.fst ⊔ q.fst :=
  PartialOrder.rel_antisymm
    (join_le p q (p.fst ⊔ q.fst, p.snd ⊔ q.snd)
      (And.intro (left_le_join _ _) (left_le_join _ _))
      (And.intro (right_le_join _ _) (right_le_join _ _))).1
    (join_le _ _ _ (left_le_join p q).1 (right_le_join p q).1)

theorem Prod.snd_join (p q : α × β) : (p ⊔ q).snd = p.snd ⊔ q.snd :=
  PartialOrder.rel_antisymm
    (join_le p q (p.fst ⊔ q.fst, p.snd ⊔ q.snd)
      (And.intro (left_le_join _ _) (left_le_join _ _))
      (And.intro (right_le_join _ _) (right_le_join _ _))).2
    (join_le _ _ _ (left_le_join p q).2 (right_le_join p q).2)

theorem Prod.fst_iSup {ι : Type w} (f : ι → α × β) : (iSup f).fst = ⨆ i, (f i).fst :=
  PartialOrder.rel_antisymm
    (iSup_le f (⨆ i, (f i).fst, ⨆ i, (f i).snd)
      fun i => And.intro (le_iSup (fun i => (f i).fst) i) (le_iSup (fun i => (f i).snd) i)).1
    (iSup_le _ _ fun i => (le_iSup f i).1)

theorem Prod.snd_iSup {ι : Type w} (f : ι → α × β) : (iSup f).snd = ⨆ i, (f i).snd :=
  PartialOrder.rel_antisymm
    (iSup_le f (⨆ i, (f i).fst, ⨆ i, (f i).snd)
      fun i => And.intro (le_iSup (fun i => (f i).fst) i) (le_iSup (fun i => (f i).snd) i)).2
    (iSup_le _ _ fun i => (le_iSup f i).2)

theorem Prod.fst_iInf {ι : Type w} (f : ι → α × β) : (iInf f).fst = ⨅ i, (f i).fst :=
  PartialOrder.rel_antisymm
    (le_iInf _ _ fun i => (iInf_le f i).1)
    (le_iInf f (⨅ i, (f i).fst, ⨅ i, (f i).snd)
      fun i => Prod.mk_le _ _ _ (iInf_le (fun i => (f i).fst) i)
        (iInf_le (fun i => (f i).snd) i)).1

theorem Prod.snd_iInf {ι : Type w} (f : ι → α × β) : (iInf f).snd = ⨅ i, (f i).snd :=
  PartialOrder.rel_antisymm
    (le_iInf _ _ fun i => (iInf_le f i).2)
    (le_iInf f (⨅ i, (f i).fst, ⨅ i, (f i).snd)
      fun i => Prod.mk_le _ _ _ (iInf_le (fun i => (f i).fst) i)
        (iInf_le (fun i => (f i).snd) i)).2

theorem Prod.mk_sup (c : α × β → Prop) :
    ((CompleteLattice.sup fun a => ∃ b, c (a, b),
      CompleteLattice.sup fun b => ∃ a, c (a, b)) : α × β) = CompleteLattice.sup c :=
  prod_eq_of_pprod_eq <| by rw [prod_sup_toPProd, ← PProd.mk_sup]

theorem Prod.fst_sup (c : α × β → Prop) :
    (CompleteLattice.sup c).fst = CompleteLattice.sup fun a => ∃ b, c (a, b) := by
  rw [← Prod.mk_sup]

theorem Prod.snd_sup (c : α × β → Prop) :
    (CompleteLattice.sup c).snd = CompleteLattice.sup fun b => ∃ a, c (a, b) := by
  rw [← Prod.mk_sup]

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

end Prod

section Prod

variable {α : Type u} {β : Type v} [CompleteLattice α] [CompleteLattice β]

theorem Prod.fst_ofProp (p : Prop) : (⌜p⌝ : α × β).fst = ⌜p⌝ := by
  by_cases hp : p <;>
    simp only [CompleteLattice.ofProp, hp, ↓reduceIte, Prod.fst_top, Prod.fst_bot]

theorem Prod.snd_ofProp (p : Prop) : (⌜p⌝ : α × β).snd = ⌜p⌝ := by
  by_cases hp : p <;>
    simp only [CompleteLattice.ofProp, hp, ↓reduceIte, Prod.snd_top, Prod.snd_bot]

theorem Prod.fst_himp (a b : α × β) : (a ⇨ b).fst = a.fst ⇨ b.fst := by
  unfold himp PreservesSup.upperAdjoint
  rw [Prod.fst_sup]
  congr 1
  funext x
  apply propext
  constructor
  · rintro ⟨y, h⟩
    exact Prod.fst_meet a (x, y) ▸ h.1
  · intro h
    exact ⟨⊥, (Prod.fst_meet a (x, ⊥)).symm ▸ h,
      (Prod.snd_meet a (x, ⊥)).symm ▸ rel_trans (meet_le_right _ _) (bot_le _)⟩

theorem Prod.snd_himp (a b : α × β) : (a ⇨ b).snd = a.snd ⇨ b.snd := by
  unfold himp PreservesSup.upperAdjoint
  rw [Prod.snd_sup]
  congr 1
  funext y
  apply propext
  constructor
  · rintro ⟨x, h⟩
    exact Prod.snd_meet a (x, y) ▸ h.2
  · intro h
    exact ⟨⊥, (Prod.fst_meet a (⊥, y)).symm ▸ rel_trans (meet_le_right _ _) (bot_le _),
      (Prod.snd_meet a (⊥, y)).symm ▸ h⟩

end Prod

end Lean.Order

end -- public section
