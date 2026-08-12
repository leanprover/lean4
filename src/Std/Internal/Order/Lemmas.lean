/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Gladshtein, Sebastian Graf
-/
module

prelude
public import Std.Internal.Order.Basic
public import Std.Internal.Order.PropLattice
public import Init.ByCases
import Init.Classical
import Init.TacticsExtra

@[expose] public section

/-!
# Complete lattice algebra

The laws of `⊤`, `⊥`, `⊓`, `⊔`, `⨅` and `⨆`, their pointwise characterizations on function
lattices, and the laws of the `Prop` lattice.
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

theorem iInf_le {ι : Type vₗ} (f : ι → α) (i : ι) : iInf f ⊑ f i := by
  apply inf_le
  exact ⟨i, rfl⟩

theorem le_iInf {ι : Type vₗ} (f : ι → α) (x : α) : (∀ i, x ⊑ f i) → x ⊑ iInf f := by
  intro h
  apply le_inf
  intro y ⟨i, hi⟩
  rw [← hi]
  exact h i

/-- Pointwise characterization of indexed infimum on function lattices. -/
@[simp] theorem iInf_apply
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

theorem le_iSup {ι : Type vₗ} (f : ι → α) (i : ι) : f i ⊑ iSup f := by
  apply le_sup
  exact ⟨i, rfl⟩

theorem iSup_le {ι : Type vₗ} (f : ι → α) (x : α) : (∀ i, f i ⊑ x) → iSup f ⊑ x := by
  intro h
  apply sup_le
  intro y ⟨i, hi⟩
  rw [← hi]
  exact h i

/-- Pointwise characterization of indexed supremum on function lattices. -/
@[simp] theorem iSup_apply
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
@[simp, grind =] theorem meet_apply
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
@[simp] theorem join_apply
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
@[simp] theorem top_apply {σ : Type vₗ} {β : Type wₗ} [CompleteLattice β] (s : σ) :
    (⊤ : σ → β) s = (⊤ : β) :=
  PartialOrder.rel_antisymm (le_top _) ((le_top (fun _ : σ => (⊤ : β))) s)

/-- Pointwise characterization of `⊥` on a function lattice. -/
@[simp] theorem bot_apply {σ : Type vₗ} {β : Type wₗ} [CompleteLattice β] (s : σ) :
    (⊥ : σ → β) s = (⊥ : β) :=
  PartialOrder.rel_antisymm ((bot_le (fun _ : σ => (⊥ : β))) s) (bot_le _)

@[grind =, simp] theorem le_prop_eq_imp (p q : Prop) : (p ⊑ q) = (p → q) := rfl

/-- Entailment on a function lattice is pointwise. `β` is recoverable from the operands' types, so
unlike a carrier-only parameter this is a usable `@[grind =]` trigger; it lets `grind` push `⊑`
through a state argument down to the base lattice. -/
@[grind =] theorem le_pi_eq_forall {σ : Type vₗ} {β : σ → Type wₗ} [∀ s, PartialOrder (β s)]
    (a b : ∀ s, β s) : (a ⊑ b) = ∀ s, a s ⊑ b s := rfl

theorem le_of_imp_top_le (x y : Prop) : (x → (⊤ : Prop) ⊑ y) → x ⊑ y :=
  fun h hx => h hx (le_top True trivial)

theorem top_le_prop (x : Prop) : x → (⊤ : Prop) ⊑ x :=
  fun hx _ => hx

theorem le_of_right (x y : Prop) : y → x ⊑ y :=
  fun hy _ => hy

theorem of_top_le_prop {x : Prop} : (⊤ : Prop) ⊑ x → x :=
  fun h => h (le_top True trivial)

theorem true_le_of_top_le (x : Prop) : ((⊤ : Prop) ⊑ x) → (True : Prop) ⊑ x :=
  fun h => le_of_right True x (of_top_le_prop h)

@[simp] theorem iInf_prop_eq_forall {ι : Type uₗ} (f : ι → Prop) :
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

@[simp] theorem iSup_prop_eq_exists {ι : Type uₗ} (f : ι → Prop) :
    (iSup f : Prop) = (∃ i, f i) := by
  apply propext
  constructor
  · intro hsup
    exact (iSup_le f (x := ∃ i, f i) (fun i hi => ⟨i, hi⟩)) hsup
  · intro ⟨i, hi⟩
    exact (le_iSup f i) hi

@[grind =, simp] theorem meet_prop_eq_and (a b : Prop) : (a ⊓ b : Prop) = (a ∧ b) := by
  apply propext
  constructor
  · intro hab
    exact ⟨(meet_le_left a b) hab, (meet_le_right a b) hab⟩
  · intro hab
    exact (le_meet (a ∧ b) a b (fun h => h.left) (fun h => h.right)) hab

@[simp] theorem join_prop_eq_or (a b : Prop) : (a ⊔ b : Prop) = (a ∨ b) := by
  apply propext
  constructor
  · intro hab
    exact (join_le a b (a ∨ b) (fun ha => Or.inl ha) (fun hb => Or.inr hb)) hab
  · intro hab
    cases hab with
    | inl ha => exact (left_le_join a b) ha
    | inr hb => exact (right_le_join a b) hb

/-- Entailment between functions is pointwise. -/
theorem le_iff_forall_le {σ : Type uₗ} {β : Type vₗ} [PartialOrder β] {f g : σ → β} :
    (f ⊑ g) ↔ (∀ s, f s ⊑ g s) := Iff.rfl

/-- Entailment between functions follows from pointwise entailment. -/
theorem le_of_forall_le {σ : Type uₗ} {β : Type vₗ} [PartialOrder β] {f g : σ → β} :
    (∀ s, f s ⊑ g s) → f ⊑ g := le_iff_forall_le.mpr

/-- `⊤ ⊑ g` for a function `g` follows from pointwise `⊤ ⊑ g s`. -/
theorem top_le_of_forall_top_le {σ : Type uₗ} {β : Type vₗ} [CompleteLattice β] {g : σ → β} :
    (∀ s, (⊤ : β) ⊑ g s) → (⊤ : σ → β) ⊑ g := by
  intro h s
  rw [top_apply]
  exact h s

/-- The top element of the `Prop` lattice is `True`. -/
@[grind =, simp] theorem top_prop_eq : (⊤ : Prop) = True :=
  propext ⟨fun _ => trivial, fun _ => le_top True trivial⟩

/-- The bottom element of the `Prop` lattice is `False`. -/
@[grind =, simp] theorem bot_prop_eq : (⊥ : Prop) = False :=
  propext ⟨fun h => bot_le False h, fun h => h.elim⟩

end CompleteLattice

/-! ## Derived laws of `CompleteLattice`

Lattice algebra derived from the laws of `CompleteLattice`: monotonicity of the connectives, the
monoid laws of `⊓` and `⊔` with their units `⊤` and `⊥`, and the pointwise unfoldings of `⊑` on
function lattices.
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
theorem le_trans_meet (h₁ : P ⊑ Q) (h₂ : P ⊓ Q ⊑ R) : P ⊑ R := rel_trans (le_meet _ _ _ rel_refl h₁) h₂
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

/-! ### Miscellaneous -/

theorem meet_left_comm : P ⊓ (Q ⊓ R) = Q ⊓ (P ⊓ R) := by
  rw [← meet_assoc, meet_comm (P := P), meet_assoc]
theorem meet_right_comm : (P ⊓ Q) ⊓ R = (P ⊓ R) ⊓ Q := by
  rw [meet_assoc, meet_comm (P := Q), ← meet_assoc]

/-! ### Working with entailment -/

@[simp] theorem le_top_iff : (Q ⊑ (⊤ : l)) ↔ True := iff_true_intro (le_top _)

/-! #### Pointwise unfoldings of `⊑` on function lattices

Fixed-arity instances of `le_iff_forall_le` for nested function lattices, stated separately per
arity so that `simp` and `grind` can apply them. Each is definitional via the function-space
`PartialOrder` instance. -/

@[simp] theorem le_iff_forall_le_1 {σ : Type vₗ} {P Q : σ → l} :
    P ⊑ Q ↔ ∀ s, P s ⊑ Q s := Iff.rfl
@[simp] theorem le_iff_forall_le_2 {σ₁ σ₂ : Type vₗ} {P Q : σ₁ → σ₂ → l} :
    P ⊑ Q ↔ ∀ s₁ s₂, P s₁ s₂ ⊑ Q s₁ s₂ := Iff.rfl
@[simp] theorem le_iff_forall_le_3 {σ₁ σ₂ σ₃ : Type vₗ} {P Q : σ₁ → σ₂ → σ₃ → l} :
    P ⊑ Q ↔ ∀ s₁ s₂ s₃, P s₁ s₂ s₃ ⊑ Q s₁ s₂ s₃ := Iff.rfl
@[simp] theorem le_iff_forall_le_4 {σ₁ σ₂ σ₃ σ₄ : Type vₗ} {P Q : σ₁ → σ₂ → σ₃ → σ₄ → l} :
    P ⊑ Q ↔ ∀ s₁ s₂ s₃ s₄, P s₁ s₂ s₃ s₄ ⊑ Q s₁ s₂ s₃ s₄ := Iff.rfl
@[simp] theorem le_iff_forall_le_5 {σ₁ σ₂ σ₃ σ₄ σ₅ : Type vₗ} {P Q : σ₁ → σ₂ → σ₃ → σ₄ → σ₅ → l} :
    P ⊑ Q ↔ ∀ s₁ s₂ s₃ s₄ s₅, P s₁ s₂ s₃ s₄ s₅ ⊑ Q s₁ s₂ s₃ s₄ s₅ := Iff.rfl

end CompleteLatticeAlgebra

end Lean.Order
