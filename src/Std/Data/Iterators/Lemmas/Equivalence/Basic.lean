/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Init.Control.Lawful.Basic
import Init.Ext
import Init.Internal.Order
import Init.Core
import Std.Data.Iterators.Basic
import Std.Data.Iterators.PostConditionMonad

namespace Std.Iterators

inductive IteratorUnion (α₁ α₂ : Type w) (m : Type w → Type w') (β : Type w) where
  | left : IterM (α := α₁) m β → IteratorUnion α₁ α₂ m β
  | right : IterM (α := α₂) m β → IteratorUnion α₁ α₂ m β

def mkLeft (it : IterM (α := α₁) m β) : IterM (α := IteratorUnion α₁ α₂ m β) m β :=
  ⟨.left it⟩

def mkRight (it : IterM (α := α₂) m β) : IterM (α := IteratorUnion α₁ α₂ m β) m β :=
  ⟨.right it⟩

instance [Monad m] [Iterator α₁ m β] [Iterator α₂ m β] : Iterator (IteratorUnion α₁ α₂ m β) m β where
  IsPlausibleStep
    | ⟨.left it⟩, s => ∃ s', s = s'.mapIterator mkLeft ∧ it.IsPlausibleStep s'
    | ⟨.right it⟩, s => ∃ s', s = s'.mapIterator mkRight ∧ it.IsPlausibleStep s'
  step
    | ⟨.left it⟩ => (fun x => ⟨x.1.mapIterator mkLeft, x.1, rfl, x.2⟩) <$> it.step
    | ⟨.right it⟩ => (fun x => ⟨x.1.mapIterator mkRight, x.1, rfl, x.2⟩) <$> it.step

def f {R S : α → α → Prop} (h : ∀ a b, R a b → S a b) : Quot R → Quot S :=
  Quot.lift (Quot.mk S) (fun _ _ hR => Quot.sound (h _ _ hR))

theorem fprop {R S : α → α → Prop} (h : ∀ a b, R a b → S a b) :
    Quot.mk S = (f h) ∘ Quot.mk R :=
  rfl

def g (R : α → α → Prop) : Quot R → Quot (fun a b => Quot.mk R a = Quot.mk R b) :=
  Quot.lift (Quot.mk _) (fun _ _ h => Quot.sound (Quot.sound h))

def gprop (R : α → α → Prop) : Quot.mk _ = (g R) ∘ Quot.mk _ :=
  rfl

def IterM.step' {α β : Type w} {m : Type w → Type w'} [Iterator α m β] (it : IterM (α := α) m β) :
    PostconditionT m (IterStep (IterM (α := α) m β) β) :=
  ⟨_, it.step⟩

def ItEquiv (α : Type w) (m : Type w → Type w') {β : Type w} [Iterator α m β] [Monad m] [LawfulMonad m]
    (ita itb : IterM (α := α) m β) : Prop :=
  (IterStep.mapIterator (Quot.mk (ItEquiv α m)) <$> ita.step' = IterStep.mapIterator (Quot.mk (ItEquiv α m)) <$> itb.step')
greatest_fixpoint monotonicity by
  rintro R S hRS ita itb h
  simp only [comp_map, fprop hRS, IterStep.mapIterator_comp, h]

 def ItEquiv.step {m : Type w → Type w'} [Monad m] [LawfulMonad m] {α β : Type w} [Iterator α m β]
    [Monad m] [LawfulMonad m] : Quot (ItEquiv α m) → PostconditionT m (IterStep (Quot (ItEquiv α m)) β) :=
  Quot.lift (IterStep.mapIterator (Quot.mk (ItEquiv α m)) <$> ·.step')
  (by intro a b h; rwa [ItEquiv] at h)

def ItEquiv.step_mk {m : Type w → Type w'} [Monad m] [LawfulMonad m] {α β : Type w} [Iterator α m β]
    [Monad m] [LawfulMonad m] {it : IterM (α := α) m β} :
    ItEquiv.step (Quot.mk _ it) = IterStep.mapIterator (Quot.mk (ItEquiv α m)) <$> it.step' :=
  rfl

def ItHEquiv (m : Type w →Type w') [Monad m] [LawfulMonad m]
    (β : Type w) {α₁ α₂ : Type w} [Iterator α₁ m β] [Iterator α₂ m β]
    (it₁ : IterM (α := α₁) m β) (it₂ : IterM (α := α₂) m β) : Prop :=
  ItEquiv (IteratorUnion α₁ α₂ m β) m (mkLeft it₁) (mkRight it₂)

theorem ItEquiv.of_mk_eq_mk {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β] [Monad m] [LawfulMonad m]
    (ita itb : IterM (α := α) m β) : Quot.mk (ItEquiv α m) ita = Quot.mk (ItEquiv α m) itb → ItEquiv α m ita itb := by
  refine ItEquiv.fixpoint_induct α m (fun ita' itb' => Quot.mk _ ita' = Quot.mk _ itb') ?_ ita itb
  intro ita' itb' h
  rw [gprop, IterStep.mapIterator_comp, comp_map, comp_map]
  replace h := congrArg ItEquiv.step h
  simp only [step_mk] at  h
  simp only [h]

theorem ItEquiv.refl {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β] [Monad m] [LawfulMonad m]
    (it : IterM (α := α) m β) : ItEquiv α m it it :=
  of_mk_eq_mk it it rfl

theorem ItEquiv.symm {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β] [Monad m] [LawfulMonad m]
    {ita itb : IterM (α := α) m β} (h : ItEquiv α m ita itb) : ItEquiv α m itb ita :=
  of_mk_eq_mk itb ita (Quot.sound h).symm

theorem ItEquiv.trans {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β] [Monad m] [LawfulMonad m]
    {ita itb itc : IterM (α := α) m β} (hab : ItEquiv α m ita itb) (hbc : ItEquiv α m itb itc) : ItEquiv α m ita itc :=
  of_mk_eq_mk ita itc (Eq.trans (Quot.sound hab) (Quot.sound hbc))

theorem step'_mkLeft {α₁ α₂ β : Type w} {m : Type w → Type w'} [Iterator α₁ m β] [Iterator α₂ m β]
    [Monad m] [LawfulMonad m] {it : IterM (α := α₁) m β} :
    (mkLeft (α₂ := α₂) it).step' = (·.mapIterator mkLeft) <$> it.step' := by sorry

theorem step'_mkRight {α₁ α₂ β : Type w} {m : Type w → Type w'} [Iterator α₁ m β] [Iterator α₂ m β]
    [Monad m] [LawfulMonad m] {it : IterM (α := α₂) m β} :
    (mkRight (α₁ := α₁) it).step' = (·.mapIterator mkRight) <$> it.step' := by sorry

theorem exists_iterStep_of_iterstep_quot {α β : Type w} {R : α → α → Prop}
    (step : IterStep (Quot R) β) : ∃ step' : IterStep α β, step = step'.mapIterator (Quot.mk _) := by
  cases step
  · rename_i it out
    rcases it with ⟨it⟩
    exact ⟨.yield it out, rfl⟩
  · rename_i it
    rcases it with ⟨it⟩
    exact ⟨.skip it, rfl⟩
  · exact ⟨.done, rfl⟩

theorem ItHEquiv.refl_aux {α β : Type w} {m : Type w → Type w'}
    [Iterator α m β] [Monad m] [LawfulMonad m] {ita itb : IterM (α := α) m β} :
    ItEquiv (IteratorUnion α α m β) m (mkLeft ita) (mkRight itb) ↔ ItEquiv α m ita itb := by
  constructor
  · intro h
    refine ItEquiv.fixpoint_induct _ _ (fun ita' itb' => ItEquiv (IteratorUnion α α m β) m (mkLeft ita') (mkRight itb')) ?implies ita itb h
    intro ita' itb' h'
    rw [ItEquiv] at h'
    simp only [step'_mkLeft, step'_mkRight, Functor.map_map] at h'
    rw [PostconditionT.ext_iff]
    rw [PostconditionT.ext_iff] at h'
    obtain ⟨h₁, h₂⟩ := h'
    refine ⟨?_, ?_⟩
    · ext step
      replace h₁ := funext_iff.mp h₁
      obtain ⟨step, rfl⟩ := exists_iterStep_of_iterstep_quot step
      constructor
      · rintro ⟨s, h⟩

theorem ItHEquiv.refl {α : Type w} {m : Type w → Type w'} {β : Type w}
    [Iterator α m β] [Monad m] [LawfulMonad m]
    (it : IterM (α := α) m β) : ItHEquiv m β it it := by
  rw [ItHEquiv]
  apply ItEquiv.refl

theorem ItHEquiv.refl {α₁ α₂ : Type w} {m : Type w → Type w'} {β : Type w}
    [Iterator α₁ m β] [Iterator α₂ m β] [Monad m] [LawfulMonad m]
    (ita : IterM (α := α₁) m β) (itb : IterM (α := α₂) m β) : ItHEquiv m it it :=
  of_mk_eq_mk it it rfl

theorem ItHEquiv.symm {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β] [Monad m] [LawfulMonad m]
    {ita itb : IterM (α := α) m β} (h : ItEquiv α m ita itb) : ItEquiv α m itb ita :=
  of_mk_eq_mk itb ita (Quot.sound h).symm

theorem ItHEquiv.trans {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β] [Monad m] [LawfulMonad m]
    {ita itb itc : IterM (α := α) m β} (hab : ItEquiv α m ita itb) (hbc : ItEquiv α m itb itc) : ItEquiv α m ita itc :=
  of_mk_eq_mk ita itc (Eq.trans (Quot.sound hab) (Quot.sound hbc))

def X (f g : α × (α → β × α)) : Prop := Quotient.mk ⟨fun (p q : β × (α × (α → β × α))) => X p.2 q.2, sorry⟩ ((f.2 f.1).1, ((f.2 f.1).2, f.2)) = Quotient.mk ⟨_, sorry⟩ ((g.2 g.1).1, ((g.2 g.1).2, g.2))
greatest_fixpoint monotonicity
  by
    intro R S hRS

structure IterM.PlausibilityMorphism (α α' : Type w) (m : Type w → Type w') {β : Type w}
    [Iterator α m β] [Iterator α' m β] where
  map : IterM (α := α) m β → IterM (α := α') m β
  IsPlausibleStep_map : ∀ {it : IterM (α := α) m β} {step : IterStep (IterM (α := α) m β) β},
      (map it).IsPlausibleStep (step.mapIterator map) ↔ ∃ step', step'.mapIterator map = step.mapIterator map ∧ it.IsPlausibleStep step'

def IterM.PlausibilityMorphism.mapStep {α α' : Type w} {m : Type w → Type w'} {β : Type w}
    [Iterator α m β] [Iterator α' m β] (φ : PlausibilityMorphism α α' m)
    {it : IterM (α := α) m β} (step : it.Step) : (φ.map it).Step :=
  ⟨step.1.mapIterator φ.map, φ.IsPlausibleStep_map.mpr step.2⟩

structure IterM.Morphism (α α' : Type w) (m : Type w → Type w') [Functor m] {β : Type w}
    [Iterator α m β] [Iterator α' m β] extends IterM.PlausibilityMorphism α α' m where
  stepH_hom : ∀ {it : IterM (α := α) m β},
      toPlausibilityMorphism.mapStep <$> it.step = (map it).step

def IterM.Morphism.id (α : Type w) (m : Type w → Type w') [Functor m] [LawfulFunctor m] {β : Type w} [Iterator α m β] :
    Morphism α α m where
  map it := it
  IsPlausibleStep_map {it step} := by
    change it.IsPlausibleStep (step.mapIterator _root_.id) ↔ it.IsPlausibleStep step
    simp [IterStep.mapIterator_id]
  stepH_hom {it} := by
    conv => rhs; rw [← id_map (x := it.step)]
    refine congrArg (· <$> _) ?_
    ext step
    obtain ⟨step, _⟩ := step
    cases step <;> simp [PlausibilityMorphism.mapStep]

def IterM.Morphism.copy {α α' : Type w} {m : Type w → Type w'} [Functor m] {β : Type w}
    [Iterator α m β] [Iterator α' m β] (φ : Morphism α α' m) {f : IterM (α := α) m β → IterM (α := α') m β}
    (h : f = φ.map) : Morphism α α' m where
  map := f
  IsPlausibleStep_map := h ▸ φ.IsPlausibleStep_map
  stepH_hom := by cases h; exact φ.stepH_hom

end Std.Iterators
