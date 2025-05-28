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

instance (bit : BundledIterM m β) : Iterator bit.α m β :=
  bit.inst

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

def ItEquiv (m : Type w → Type w') (β : Type w) [Monad m] [LawfulMonad m]
    (ita itb : BundledIterM m β) : Prop :=
  (CodensityT.lift ita.iterator.step').map (IterStep.mapIterator (Quot.mk (ItEquiv m β) ∘ BundledIterM.ofIterM)) =
    (CodensityT.lift itb.iterator.step').map (IterStep.mapIterator (Quot.mk (ItEquiv m β) ∘ BundledIterM.ofIterM))
greatest_fixpoint monotonicity by
  rintro R S hRS ita itb h
  simp only [IterStep.mapIterator_comp, CodensityT.comp_map, Function.comp_apply] at h
  simp only [fprop hRS, IterStep.mapIterator_comp, CodensityT.comp_map, Function.comp_apply, h]

 def ItEquiv.step {m : Type w → Type w'} [Monad m] [LawfulMonad m] {β : Type w}
    [Monad m] [LawfulMonad m] : Quot (ItEquiv m β) → CodensityT (PostconditionT m) (IterStep (Quot (ItEquiv m β)) β) :=
  Quot.lift (fun bit => (CodensityT.lift bit.iterator.step').map <| IterStep.mapIterator (Quot.mk (ItEquiv m β) ∘ BundledIterM.ofIterM))
    (by intro ita itb h; rwa [ItEquiv] at h)

def ItEquiv.step_mk {m : Type w → Type w'} [Monad m] [LawfulMonad m] {β : Type w}
    [Monad m] [LawfulMonad m] {bit} :
    ItEquiv.step (Quot.mk _ bit) = (CodensityT.lift bit.iterator.step').map (IterStep.mapIterator (Quot.mk (ItEquiv m β) ∘ BundledIterM.ofIterM)) :=
  rfl

protected theorem ItEquiv.exact {m : Type w → Type w'} {β : Type w} [Monad m] [LawfulMonad m]
    (ita itb : BundledIterM m β) : Quot.mk (ItEquiv m β) ita = Quot.mk (ItEquiv m β) itb → ItEquiv m β ita itb := by
  refine ItEquiv.fixpoint_induct m β (fun ita' itb' => Quot.mk _ ita' = Quot.mk _ itb') ?_ ita itb
  intro ita' itb' h
  simp [gprop, IterStep.mapIterator_comp, CodensityT.comp_map, comp_map]
  replace h := congrArg ItEquiv.step h
  simp [step_mk, step_mk, CodensityT.comp_map, funext_iff] at h
  simp [IterStep.mapIterator_comp, CodensityT.comp_map] at h
  simp only [h]

theorem ItEquiv.refl {m : Type w → Type w'} {β : Type w} [Monad m] [LawfulMonad m]
    (it) : ItEquiv m β it it :=
  ItEquiv.exact it it rfl

theorem ItEquiv.symm {m : Type w → Type w'} {β : Type w} [Monad m] [LawfulMonad m]
    {ita itb} (h : ItEquiv m β ita itb) : ItEquiv m β itb ita :=
  ItEquiv.exact itb ita (Quot.sound h).symm

theorem ItEquiv.trans {m : Type w → Type w'} {β : Type w} [Monad m] [LawfulMonad m]
    {ita itb itc} (hab : ItEquiv m β ita itb) (hbc : ItEquiv m β itb itc) : ItEquiv m β ita itc :=
  ItEquiv.exact ita itc (Eq.trans (Quot.sound hab) (Quot.sound hbc))

def HItEquiv {m : Type w → Type w'} [Monad m] [LawfulMonad m] {β : Type w} {α₁ α₂} [Iterator α₁ m β] [Iterator α₂ m β]
    (ita : IterM (α := α₁) m β) (itb : IterM (α := α₂) m β) :=
  ItEquiv m β (BundledIterM.ofIterM ita) (BundledIterM.ofIterM itb)

theorem HItEquiv.refl {m : Type w → Type w'} {β : Type w} [Monad m] [LawfulMonad m]
    {α : Type w} [Iterator α m β] (it : IterM (α := α) m β) : HItEquiv it it :=
  ItEquiv.refl _

theorem ItEquiv.of_morphism {α₁ α₂} {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    {β : Type w} [Iterator α₁ m β] [Iterator α₂ m β]
    (ita : IterM (α := α₁) m β)
    (f : IterM (α := α₁) m β → IterM (α := α₂) m β) (h : ∀ it, (f it).step' = IterStep.mapIterator f <$> it.step') :
    HItEquiv ita (f ita) := by
  refine ItEquiv.fixpoint_induct m β ?R ?implies (.ofIterM ita) (.ofIterM (f ita)) ?hf
  case R =>
    intro ita itb
    exact ∃ it, ita = .ofIterM it ∧ itb = .ofIterM (f it)
  case implies =>
    rintro _ _ ⟨it, rfl, rfl⟩
    simp [show (BundledIterM.ofIterM (f it)).iterator = f it by rfl,
      show (BundledIterM.ofIterM it).iterator = it by rfl,
      h, CodensityT.lift_map]
    simp [CodensityT.map_map]
    congr
    apply congrArg (CodensityT.map · _)
    ext step
    simp [IterStep.mapIterator_mapIterator]
    congr
    ext it
    simp
    apply Quot.sound
    exact ⟨it, rfl, rfl⟩
  case hf =>
    exact ⟨ita, rfl, rfl⟩

end Std.Iterators
