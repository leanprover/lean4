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
import Std.Data.Iterators.Lemmas.Equivalence.HetT

namespace Std.Iterators

structure BundledIterM (m : Type w → Type w') (β : Type w) where
  α : Type w
  inst : Iterator α m β
  iterator : IterM (α := α) m β

def BundledIterM.ofIterM {α} [Iterator α m β] (it : IterM (α := α) m β) :
    BundledIterM m β :=
  ⟨α, inferInstance, it⟩

@[simp]
theorem BundledIterM.iterator_ofIterM {α} [Iterator α m β] (it : IterM (α := α) m β) :
    (BundledIterM.ofIterM it).iterator = it :=
  rfl

instance (bit : BundledIterM m β) : Iterator bit.α m β :=
  bit.inst

def Todo.f {R S : α → α → Prop} (h : ∀ a b, R a b → S a b) : Quot R → Quot S :=
  Quot.lift (Quot.mk S) (fun _ _ hR => Quot.sound (h _ _ hR))

theorem fprop {R S : α → α → Prop} (h : ∀ a b, R a b → S a b) :
    Quot.mk S = (Todo.f h) ∘ Quot.mk R :=
  rfl

def Todo.g (R : α → α → Prop) : Quot R → Quot (fun a b => Quot.mk R a = Quot.mk R b) :=
  Quot.lift (Quot.mk _) (fun _ _ h => Quot.sound (Quot.sound h))

def gprop (R : α → α → Prop) : Quot.mk _ = (Todo.g R) ∘ Quot.mk _ :=
  rfl

noncomputable def IterM.step' [Iterator α m β] [Monad m] (it : IterM (α := α) m β) :
    HetT m (IterStep (IterM (α := α) m β) β) :=
    ⟨it.IsPlausibleStep, inferInstance, (fun step => .deflate step) <$> it.step⟩

@[simp]
theorem IterM.property_step' [Iterator α m β] [Monad m] [LawfulMonad m] {it : IterM (α := α) m β} :
    it.step'.Property = it.IsPlausibleStep :=
  rfl

@[simp]
theorem IterM.prun_step' [Iterator α m β] [Monad m] [LawfulMonad m] {it : IterM (α := α) m β}
    {f : (step : _) → _ → m γ} :
    it.step'.prun f = it.step >>= (fun step => f step.1 step.2) := by
  simp [IterM.step', HetT.prun, IterM.Step, PlausibleIterStep]

@[simp]
theorem IterM.prun_liftInner_step' [Iterator α m β] [Monad m] [Monad n] [MonadLiftT m n]
    [LawfulMonad m] [LawfulMonad n] [LawfulMonadLiftT m n] {it : IterM (α := α) m β}
    {f : (step : _) → _ → n γ} :
    (it.step'.liftInner n).prun f = (it.step : n _) >>= (fun step => f step.1 step.2) := by
  simp [IterM.step', HetT.liftInner, HetT.prun, IterM.Step, PlausibleIterStep]

noncomputable def BundledIterM.step' {α β : Type w} {m : Type w → Type w'} [Monad m] [LawfulMonad m] [Iterator α m β] (R : BundledIterM m β → BundledIterM m β → Prop)
    (it : IterM (α := α) m β) :
    HetT m (IterStep (Quot R) β) :=
  it.step'.map (IterStep.mapIterator (Quot.mk _ ∘ BundledIterM.ofIterM))
  -- ⟨fun step => ∃ step', it.IsPlausibleStep step' ∧ step = step'.mapIterator (Quot.mk _ ∘ BundledIterM.ofIterM),
  --   fun f => it.step >>= fun step' => f (step'.1.mapIterator (Quot.mk _ ∘ BundledIterM.ofIterM)) ⟨step'.1, step'.2, rfl⟩⟩

def ItEquiv (m : Type w → Type w') (β : Type w) [Monad m] [LawfulMonad m]
    (ita itb : BundledIterM m β) : Prop :=
  BundledIterM.step' (ItEquiv m β) ita.iterator = BundledIterM.step' (ItEquiv m β) itb.iterator
greatest_fixpoint monotonicity by
  intro R S hRS ita itb h
  simp only [BundledIterM.step', IterStep.mapIterator_comp, HetT.comp_map] at ⊢ h
  simp only [fprop hRS, IterStep.mapIterator_comp, HetT.comp_map, h]

noncomputable def BundledIterM.stepQ {β : Type w} {m : Type w → Type w'} [Monad m] [LawfulMonad m] :
    Quot (ItEquiv m β) → HetT m (IterStep (Quot (ItEquiv m β)) β) :=
  Quot.lift (fun bit => step' _ bit.iterator)
    (by
      intro ita itb h
      rwa [ItEquiv] at h)

--  def ItEquiv.step {m : Type w → Type w'} [Monad m] [LawfulMonad m] {β : Type w}
--     [Monad m] [LawfulMonad m] : Quot (ItEquiv m β) → CodensityT (PostconditionT m) (IterStep (Quot (ItEquiv m β)) β) :=
--   Quot.lift (fun bit => (CodensityT.lift bit.iterator.step').map <| IterStep.mapIterator (Quot.mk (ItEquiv m β) ∘ BundledIterM.ofIterM))
--     (by intro ita itb h; rwa [ItEquiv] at h)

def BundledIterM.stepQ_mk {m : Type w → Type w'} [Monad m] [LawfulMonad m] {β : Type w}
    [Monad m] [LawfulMonad m] {bit : BundledIterM m β} :
    stepQ (Quot.mk _ bit) = step' _ bit.iterator :=
  rfl

protected theorem ItEquiv.exact {m : Type w → Type w'} {β : Type w} [Monad m] [LawfulMonad m]
    (ita itb : BundledIterM m β) : Quot.mk (ItEquiv m β) ita = Quot.mk (ItEquiv m β) itb → ItEquiv m β ita itb := by
  refine ItEquiv.fixpoint_induct m β (fun ita' itb' => Quot.mk _ ita' = Quot.mk _ itb') ?_ ita itb
  intro ita' itb' h
  replace h := congrArg (BundledIterM.stepQ) h
  simp only [BundledIterM.stepQ_mk, BundledIterM.step', IterStep.mapIterator_comp, HetT.comp_map] at h
  simp only [BundledIterM.step', gprop, IterStep.mapIterator_comp, HetT.comp_map]
  simp only [h]

protected theorem ItEquiv.quotMk_eq_iff {m : Type w → Type w'} {β : Type w} [Monad m] [LawfulMonad m]
    (ita itb : BundledIterM m β) : Quot.mk (ItEquiv m β) ita = Quot.mk (ItEquiv m β) itb ↔ ItEquiv m β ita itb := by
  constructor
  · apply ItEquiv.exact
  · exact Quot.sound

theorem ItEquiv.refl {m : Type w → Type w'} {β : Type w} [Monad m] [LawfulMonad m]
    (it) : ItEquiv m β it it :=
  ItEquiv.exact it it rfl

theorem ItEquiv.symm {m : Type w → Type w'} {β : Type w} [Monad m] [LawfulMonad m]
    {ita itb} (h : ItEquiv m β ita itb) : ItEquiv m β itb ita :=
  ItEquiv.exact itb ita (Quot.sound h).symm

theorem ItEquiv.trans {m : Type w → Type w'} {β : Type w} [Monad m] [LawfulMonad m]
    {ita itb itc} (hab : ItEquiv m β ita itb) (hbc : ItEquiv m β itb itc) : ItEquiv m β ita itc :=
  ItEquiv.exact ita itc (Eq.trans (Quot.sound hab) (Quot.sound hbc))

def HItEquivM {m : Type w → Type w'} [Monad m] [LawfulMonad m] {β : Type w} {α₁ α₂}
    [Iterator α₁ m β] [Iterator α₂ m β]
    (ita : IterM (α := α₁) m β) (itb : IterM (α := α₂) m β) :=
  ItEquiv m β (BundledIterM.ofIterM ita) (BundledIterM.ofIterM itb)

def HItEquiv {α₁ α₂ β} [Iterator α₁ Id β] [Iterator α₂ Id β]
    (ita : Iter (α := α₁) β) (itb : Iter (α := α₂) β) :=
  HItEquivM ita.toIterM itb.toIterM

theorem HItEquiv.toIterM {α₁ α₂ β} [Iterator α₁ Id β] [Iterator α₂ Id β]
    {ita : Iter (α := α₁) β} {itb : Iter (α := α₂) β} (h : HItEquiv ita itb) :
    HItEquivM ita.toIterM itb.toIterM :=
  h

theorem HItEquivM.refl {m : Type w → Type w'} {β : Type w} [Monad m] [LawfulMonad m]
    {α : Type w} [Iterator α m β] (it : IterM (α := α) m β) : HItEquivM it it :=
  ItEquiv.refl _

theorem ItEquiv.of_morphism {α₁ α₂} {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    {β : Type w} [Iterator α₁ m β] [Iterator α₂ m β]
    (ita : IterM (α := α₁) m β)
    (f : IterM (α := α₁) m β → IterM (α := α₂) m β) (h : ∀ it, (f it).step' = IterStep.mapIterator f <$> it.step') :
    HItEquivM ita (f ita) := by
  refine ItEquiv.fixpoint_induct m β ?R ?implies (.ofIterM ita) (.ofIterM (f ita)) ?hf
  case R =>
    intro ita itb
    exact ∃ it, ita = .ofIterM it ∧ itb = .ofIterM (f it)
  case implies =>
    rintro _ _ ⟨it, rfl, rfl⟩
    simp [BundledIterM.step',
      show (BundledIterM.ofIterM (f it)).iterator = f it by rfl,
      show (BundledIterM.ofIterM it).iterator = it by rfl,
      h, Functor.map, HetT.ext_iff]
    refine ⟨?_, ?_⟩
    · unfold BundledIterM.ofIterM
      simp
      ext step
      constructor
      all_goals
        rintro ⟨step', hs', h⟩
        refine ⟨step', hs', ?_⟩
        rw [← h]
        congr
        ext it
      · apply Eq.symm
        apply Quot.sound
        refine ⟨it, rfl, rfl⟩
      · apply Quot.sound
        refine ⟨it, rfl, rfl⟩
    · intro β f
      apply bind_congr
      intro step
      congr
      ext it
      apply Quot.sound
      exact ⟨it, rfl, rfl⟩
  case hf =>
    exact ⟨ita, rfl, rfl⟩

end Std.Iterators
