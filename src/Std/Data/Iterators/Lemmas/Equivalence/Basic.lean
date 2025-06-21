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
import Init.Data.Iterators.Basic
import Init.Data.Iterators.PostconditionMonad
import Std.Data.Iterators.Lemmas.Equivalence.HetT

namespace Std.Iterators

section Definition

/--
A type with an iterator typeclass and an inhabitant bundled together. This represents an
arbitrarily typed iterator. It only exists for the construction of the equivalence relation
on iterators.

This type is not meant to be used in executable code. Unbundled `Iter` or `IterM` iterators of a
specific type have better library support and are more efficient.
-/
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

private def quotOfQuot {R S : α → α → Prop} (h : ∀ a b, R a b → S a b) : Quot R → Quot S :=
  Quot.lift (Quot.mk S) (fun _ _ hR => Quot.sound (h _ _ hR))

private theorem quotMk_eq_quotOfQuot_comp {R S : α → α → Prop} (h : ∀ a b, R a b → S a b) :
    Quot.mk S = (quotOfQuot h) ∘ Quot.mk R :=
  rfl

private theorem quotMk_quot_eq_quot_eq_quotOfQuot_comp (R : α → α → Prop) :
    Quot.mk (Quot.mk R · = Quot.mk R ·) =
    (quotOfQuot fun _ _ => Quot.sound) ∘ Quot.mk R := by
  apply quotMk_eq_quotOfQuot_comp

/--
A noncomputable variant of `IterM.step` using the `HetT` monad.
It is used in the definition of the equivalence relations on iterators,
namely `IterM.Equiv` and `Iter.Equiv`.
-/
noncomputable def IterM.stepAsHetT [Iterator α m β] [Monad m] (it : IterM (α := α) m β) :
    HetT m (IterStep (IterM (α := α) m β) β) :=
    ⟨it.IsPlausibleStep, inferInstance, (fun step => .deflate step) <$> it.step⟩

/-
Makes a step with a bundled iterator in the `HetT` monad.
-/
noncomputable def BundledIterM.step {β : Type w} {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    (it : BundledIterM m β) :
    HetT m (IterStep (BundledIterM m β) β) :=
  (IterM.stepAsHetT it.iterator).map (IterStep.mapIterator BundledIterM.ofIterM)

/--
Equivalence relation on bundled iterators.

Two bundled iterators are equivalent if they have the same `Iterator.IsPlausibleStep` relation
and their step functions are the same *up to equivalence of the successor iterators*. This
coinductive definition captures the idea that the only relevant feature of an iterator is its step
function. Other information retrievable from the iterator -- for example, whether it is a list
iterator or an array iterator -- is totally irrelevant for the equivalence judgement.
-/
def BundledIterM.Equiv (m : Type w → Type w') (β : Type w) [Monad m] [LawfulMonad m]
    (ita itb : BundledIterM m β) : Prop :=
  (BundledIterM.step ita).map (IterStep.mapIterator (Quot.mk (BundledIterM.Equiv m β))) =
  (BundledIterM.step itb).map (IterStep.mapIterator (Quot.mk (BundledIterM.Equiv m β)))
greatest_fixpoint monotonicity by
  intro R S hRS ita itb h
  simp only [BundledIterM.step] at ⊢ h
  simp only [quotMk_eq_quotOfQuot_comp hRS, IterStep.mapIterator_comp, HetT.comp_map, h]

end Definition

@[simp]
theorem Equivalence.prun_liftInner_step [Iterator α m β] [Monad m] [Monad n]
    [MonadLiftT m n] [LawfulMonad m] [LawfulMonad n] [LawfulMonadLiftT m n]
    {it : IterM (α := α) m β} {f : (step : _) → _ → n γ} :
    ((IterM.stepAsHetT it).liftInner n).prun f =
      (it.step : n _) >>= (fun step => f step.1 step.2) := by
  simp [IterM.stepAsHetT, HetT.liftInner, HetT.prun, PlausibleIterStep]

@[simp]
theorem Equivalence.property_step [Iterator α m β] [Monad m] [LawfulMonad m]
    {it : IterM (α := α) m β} : (IterM.stepAsHetT it).Property = it.IsPlausibleStep :=
  rfl

@[simp]
theorem Equivalence.prun_step [Iterator α m β] [Monad m] [LawfulMonad m]
    {it : IterM (α := α) m β} {f : (step : _) → _ → m γ} :
    (IterM.stepAsHetT it).prun f = it.step >>= (fun step => f step.1 step.2) := by
  simp [IterM.stepAsHetT, HetT.prun, PlausibleIterStep]

/--
Like `BundledIterM.step`, but takes and returns iterators modulo `BundledIterM.Equiv`.
-/
noncomputable def BundledIterM.stepOnQuotient {β : Type w} {m : Type w → Type w'} [Monad m]
    [LawfulMonad m] :
    Quot (BundledIterM.Equiv m β) → HetT m (IterStep (Quot (BundledIterM.Equiv m β)) β) :=
  Quot.lift (fun bit =>
      (IterStep.mapIterator (Quot.mk (BundledIterM.Equiv m β))) <$> BundledIterM.step bit)
    (by
      intro ita itb h
      rwa [BundledIterM.Equiv] at h)

theorem BundledIterM.stepOnQuotient_mk {m : Type w → Type w'} [Monad m] [LawfulMonad m] {β : Type w}
    [Monad m] [LawfulMonad m] {bit : BundledIterM m β} :
    stepOnQuotient (Quot.mk _ bit) = (IterStep.mapIterator (Quot.mk _)) <$> BundledIterM.step bit :=
  rfl

protected theorem BundledIterM.Equiv.exact {m : Type w → Type w'} {β : Type w} [Monad m]
    [LawfulMonad m] (ita itb : BundledIterM m β) :
    Quot.mk (BundledIterM.Equiv m β) ita =
      Quot.mk (BundledIterM.Equiv m β) itb → BundledIterM.Equiv m β ita itb := by
  refine BundledIterM.Equiv.fixpoint_induct m β
    (fun ita' itb' => Quot.mk _ ita' = Quot.mk _ itb') ?_ ita itb
  intro ita' itb' h
  replace h := congrArg (BundledIterM.stepOnQuotient) h
  simp only
    [BundledIterM.stepOnQuotient_mk, BundledIterM.step, Functor.map] at h
  simp only [BundledIterM.step, quotMk_quot_eq_quot_eq_quotOfQuot_comp, IterStep.mapIterator_comp,
    HetT.comp_map]
  simp only [h]

protected theorem BundledIterM.Equiv.quotMk_eq_iff {m : Type w → Type w'} {β : Type w} [Monad m]
    [LawfulMonad m]
    (ita itb : BundledIterM m β) : Quot.mk (BundledIterM.Equiv m β) ita =
      Quot.mk (BundledIterM.Equiv m β) itb ↔ BundledIterM.Equiv m β ita itb := by
  constructor
  · apply BundledIterM.Equiv.exact
  · exact Quot.sound

theorem BundledIterM.Equiv.refl {m : Type w → Type w'} {β : Type w} [Monad m] [LawfulMonad m]
    (it) : BundledIterM.Equiv m β it it :=
  BundledIterM.Equiv.exact it it rfl

theorem BundledIterM.Equiv.symm {m : Type w → Type w'} {β : Type w} [Monad m] [LawfulMonad m]
    {ita itb} (h : BundledIterM.Equiv m β ita itb) : BundledIterM.Equiv m β itb ita :=
  BundledIterM.Equiv.exact itb ita (Quot.sound h).symm

theorem BundledIterM.Equiv.trans {m : Type w → Type w'} {β : Type w} [Monad m] [LawfulMonad m]
    {ita itb itc} (hab : BundledIterM.Equiv m β ita itb) (hbc : BundledIterM.Equiv m β itb itc) :
    BundledIterM.Equiv m β ita itc :=
  BundledIterM.Equiv.exact ita itc (Eq.trans (Quot.sound hab) (Quot.sound hbc))

/--
Equivalence relation on monadic iterators. Equivalent iterators behave the same as long as the
internal state of them is not directly inspected.

Two iterators (possibly of different types) are equivalent if they have the same
`Iterator.IsPlausibleStep` relation and their step functions are the same *up to equivalence of the
successor iterators*. This coinductive definition captures the idea that the only relevant feature
of an iterator is its step function. Other information retrievable from the iterator -- for example,
whether it is a list iterator or an array iterator -- is totally irrelevant for the equivalence
judgement.
-/
def IterM.Equiv {m : Type w → Type w'} [Monad m] [LawfulMonad m] {β : Type w} {α₁ α₂}
    [Iterator α₁ m β] [Iterator α₂ m β]
    (ita : IterM (α := α₁) m β) (itb : IterM (α := α₂) m β) :=
  BundledIterM.Equiv m β (BundledIterM.ofIterM ita) (BundledIterM.ofIterM itb)

/--
Equivalence relation on iterators. Equivalent iterators behave the same as long as the
internal state of them is not directly inspected.

Two iterators (possibly of different types) are equivalent if they have the same
`Iterator.IsPlausibleStep` relation and their step functions are the same *up to equivalence of the
successor iterators*. This coinductive definition captures the idea that the only relevant feature
of an iterator is its step function. Other information retrievable from the iterator -- for example,
whether it is a list iterator or an array iterator -- is totally irrelevant for the equivalence
judgement.
-/
def Iter.Equiv {α₁ α₂ β} [Iterator α₁ Id β] [Iterator α₂ Id β]
    (ita : Iter (α := α₁) β) (itb : Iter (α := α₂) β) :=
  IterM.Equiv ita.toIterM itb.toIterM

theorem Iter.Equiv.toIterM {α₁ α₂ β} [Iterator α₁ Id β] [Iterator α₂ Id β]
    {ita : Iter (α := α₁) β} {itb : Iter (α := α₂) β} (h : Iter.Equiv ita itb) :
    IterM.Equiv ita.toIterM itb.toIterM :=
  h

theorem IterM.Equiv.toIter {α₁ α₂ β} [Iterator α₁ Id β] [Iterator α₂ Id β]
    {ita : IterM (α := α₁) Id β} {itb : IterM (α := α₂) Id β} (h : IterM.Equiv ita itb) :
    Iter.Equiv ita.toIter itb.toIter :=
  h

theorem IterM.Equiv.refl {m : Type w → Type w'} {β : Type w} [Monad m] [LawfulMonad m]
    {α : Type w} [Iterator α m β] (it : IterM (α := α) m β) : IterM.Equiv it it :=
  BundledIterM.Equiv.refl _

theorem IterM.Equiv.symm {m : Type w → Type w'} {α₁ α₂ β : Type w} [Monad m] [LawfulMonad m]
    [Iterator α₁ m β] [Iterator α₂ m β] {ita : IterM (α := α₁) m β} {itb : IterM (α := α₂) m β}
    (h : IterM.Equiv ita itb) :
    IterM.Equiv itb ita :=
  BundledIterM.Equiv.symm h

theorem IterM.Equiv.trans {m : Type w → Type w'} {α₁ α₂ α₃ β : Type w} [Monad m] [LawfulMonad m]
    [Iterator α₁ m β] [Iterator α₂ m β] [Iterator α₃ m β] {ita : IterM (α := α₁) m β}
    {itb : IterM (α := α₂) m β} {itc : IterM (α := α₃) m β} (hab : IterM.Equiv ita itb)
    (hbc : IterM.Equiv itb itc) : IterM.Equiv ita itc :=
  BundledIterM.Equiv.trans hab hbc

theorem Iter.Equiv.refl {β : Type w}
    {α : Type w} [Iterator α Id β] (it : Iter (α := α) β) : Iter.Equiv it it :=
  BundledIterM.Equiv.refl _

theorem Iter.Equiv.symm {α₁ α₂ β : Type w}
    [Iterator α₁ Id β] [Iterator α₂ Id β] {ita : Iter (α := α₁) β} {itb : Iter (α := α₂) β}
    (h : Iter.Equiv ita itb) :
    Iter.Equiv itb ita :=
  BundledIterM.Equiv.symm h

theorem Iter.Equiv.trans {α₁ α₂ α₃ β : Type w}
    [Iterator α₁ Id β] [Iterator α₂ Id β] [Iterator α₃ Id β] {ita : Iter (α := α₁) β}
    {itb : Iter (α := α₂) β} {itc : Iter (α := α₃) β} (hab : Iter.Equiv ita itb)
    (hbc : Iter.Equiv itb itc) : Iter.Equiv ita itc :=
  BundledIterM.Equiv.trans hab hbc

theorem IterM.Equiv.of_morphism {α₁ α₂} {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    {β : Type w} [Iterator α₁ m β] [Iterator α₂ m β]
    (ita : IterM (α := α₁) m β)
    (f : IterM (α := α₁) m β → IterM (α := α₂) m β)
    (h : ∀ it, IterM.stepAsHetT (f it) = IterStep.mapIterator f <$> IterM.stepAsHetT it) :
    IterM.Equiv ita (f ita) := by
  refine BundledIterM.Equiv.fixpoint_induct m β ?R ?implies (.ofIterM ita) (.ofIterM (f ita)) ?hf
  case R =>
    intro ita itb
    exact ∃ it, ita = .ofIterM it ∧ itb = .ofIterM (f it)
  case implies =>
    rintro _ _ ⟨it, rfl, rfl⟩
    simp only [BundledIterM.step, BundledIterM.iterator_ofIterM, HetT.map_eq_pure_bind,
      HetT.bind_assoc, Function.comp_apply, HetT.pure_bind, IterStep.mapIterator_mapIterator,
      Functor.map, HetT.ext_iff, HetT.prun_bind, Equivalence.property_step, HetT.prun_pure,
      Equivalence.prun_step, HetT.property_bind, HetT.property_pure, h]
    refine ⟨?_, ?_⟩
    · unfold BundledIterM.ofIterM
      dsimp only
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
