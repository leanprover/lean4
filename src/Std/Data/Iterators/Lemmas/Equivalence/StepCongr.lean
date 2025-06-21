/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Std.Data.Iterators.Lemmas.Equivalence.Basic

/-!
This module proves that the step functions of equivalent iterators behave the same under certain
circumstances.
-/

namespace Std.Iterators

/--
This function is used in lemmas about iterator equivalence (`Iter.Equiv` and `IterM.Equiv`).

If the given step contains a successor iterator, replaces the iterator with the quotient of its
bundled version.
-/
def IterStep.bundledQuotient [Iterator α m β] [Monad m] [LawfulMonad m]
    (step : IterStep (IterM (α := α) m β) β) :
    IterStep (Quot (BundledIterM.Equiv m β)) β :=
  step.mapIterator (Quot.mk (BundledIterM.Equiv m β) ∘ BundledIterM.ofIterM)

/--
This type is used in lemmas about iterator equivalence (`Iter.Equiv` and `IterM.Equiv`).

`it.QuotStep` is the quotient of `it.Step` where two steps are identified if they agree up to
equivalence of their successor iterator.
-/
def IterM.QuotStep [Iterator α m β] [Monad m] [LawfulMonad m]
    (it : IterM (α := α) m β) :=
  Quot (fun (s₁ s₂ : it.Step) => s₁.1.bundledQuotient = s₂.1.bundledQuotient)

/--
This function is used in lemmas about iterator equivalence (`Iter.Equiv` and `IterM.Equiv`).

Returns an `IterStep` from an `IterM.QuotStep`, discarding the `IsPlausibleStep` proof.
It commutes with `IterStep.bundledQuotient` and `Quot.mk _ : it.Step → it.QuotStep`.
-/
def IterM.QuotStep.bundledQuotient [Iterator α m β] [Monad m] [LawfulMonad m]
    {it : IterM (α := α) m β} : it.QuotStep → IterStep (Quot (BundledIterM.Equiv m β)) β :=
  Quot.lift (fun s => s.1.bundledQuotient) (by intro s t; exact id)

private theorem bind_comp_eq_map_bind {m} [Monad m] [LawfulMonad m] {f : α → β}
    {g : β → m γ} {x : m α} :
    x >>= (g ∘ f) = (f <$> x) >>= g := by
  simp only [bind_map_left]; rfl

theorem IterM.Equiv.exists_step_of_step [Iterator α₁ m β] [Iterator α₂ m β] [Monad m]
    [LawfulMonad m] {ita : IterM (α := α₁) m β} {itb : IterM (α := α₂) m β}
    (h : IterM.Equiv ita itb) (s : ita.Step) :
    ∃ s' : itb.Step, s.1.bundledQuotient = s'.1.bundledQuotient := by
  rw [IterM.Equiv, BundledIterM.Equiv] at h
  replace h := congrArg HetT.Property h
  simp only [BundledIterM.step, BundledIterM.ofIterM, HetT.map_eq_pure_bind, HetT.bind_assoc,
    Function.comp_apply, HetT.pure_bind, IterStep.mapIterator_mapIterator, HetT.property_bind,
    Equivalence.property_step, HetT.property_pure, funext_iff, eq_iff_iff] at h
  specialize h s.1.bundledQuotient
  replace h := h.1 ⟨s.1, s.2, ?_⟩
  · rcases h with ⟨s', hs'⟩
    refine ⟨⟨s', hs'.1⟩, hs'.2.symm⟩
  · rfl

open Classical in
noncomputable def IterM.QuotStep.transportAlongEquiv [Iterator α₁ m β] [Iterator α₂ m β]
    [Monad m] [LawfulMonad m] {ita : IterM (α := α₁) m β} {itb : IterM (α := α₂) m β}
    (h : IterM.Equiv ita itb) : ita.QuotStep → itb.QuotStep := by
  refine Quot.lift ?_ ?_
  · intro s₁
    have := IterM.Equiv.exists_step_of_step h s₁
    exact Quot.mk _ this.choose
  · intro s₁ s₁' hs
    apply Quot.sound
    have hs₁ := (IterM.Equiv.exists_step_of_step h s₁).choose_spec
    have hs₁' := (IterM.Equiv.exists_step_of_step h s₁').choose_spec
    rw [← hs₁, ← hs₁', hs]

private theorem IterM.Equiv.step_eq.aux {α₁ α₂ : Type w} {m : Type w → Type w'} [Monad m]
    [LawfulMonad m] [Iterator α₁ m β] [Iterator α₂ m β]
    {ita : IterM (α := α₁) m β} {itb : IterM (α := α₂) m β} (h : IterM.Equiv ita itb) {s} :
    ((IterM.stepAsHetT ita).map IterStep.bundledQuotient).Property s →
      ∃ s' : itb.Step, s = s'.1.bundledQuotient := by
  intro h
  simp only [HetT.property_map] at h
  rcases h with ⟨sa, rfl, hs⟩
  rcases IterM.Equiv.exists_step_of_step h ⟨sa, hs⟩ with ⟨sb, hsb⟩
  exact ⟨sb, hsb⟩

private theorem IterM.Equiv.step_eq.aux_subtypeMk_congr {α : Type u} {P Q R : α → Prop}
    {h₁ : ∀ a, P a → R a}
    {h₂ : ∀ a, Q a → R a} (h : P = Q) :
    (fun (a : α) (ha : P a) => Subtype.mk a (h₁ a ha)) ≍
      (fun (a : α) (ha : Q a) => Subtype.mk a (h₂ a ha)) := by
  cases h
  simp

noncomputable def IterM.QuotStep.restrict [Iterator α m β] [Monad m] [LawfulMonad m]
    {it : IterM (α := α) m β}
    (step : { s : IterStep (Quot (BundledIterM.Equiv m β)) β //
        ∃ s' : it.Step, s = s'.1.bundledQuotient }) :
    it.QuotStep :=
  Quot.mk _ step.2.choose

theorem IterStep.restrict_bundle [Iterator α₁ m β] [Iterator α₂ m β] [Monad m]
    [LawfulMonad m] {ita : IterM (α := α₁) m β} {step : IterStep (IterM (α := α₂) m β) β}
    {h : ∃ s : ita.Step, step.bundledQuotient = s.1.bundledQuotient} :
    IterM.QuotStep.restrict ⟨step.bundledQuotient, h⟩ = Quot.mk _ h.choose := by
  rfl

/-
Equivalence and usage of `transportAlongEquiv` tells us:

```lean
HetT.map QuotStep.bundledQuotient (HetT.map (Quot.mk _) ita.stepAsHetT) =
  HetT.map QuotStep.bundledQuotient (HetT.map (transportAlongEquiv ∘ Quot.mk _) itb.step)
```

The difficulty in this lemma is that we want to argue that we can cancel
`HetT.map QuotStep.bundledQuotient` because `QuotStep.bundledQuotient` is injective. This
cancellation property does not hold for all monads.
-/
theorem IterM.Equiv.step_eq {α₁ α₂ : Type w} {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    [Iterator α₁ m β] [Iterator α₂ m β] {ita : IterM (α := α₁) m β} {itb : IterM (α := α₂) m β}
    (h : IterM.Equiv ita itb) :
    (Quot.mk _ : _ → ita.QuotStep) <$> ita.step =
      IterM.QuotStep.transportAlongEquiv h.symm <$> (Quot.mk _ : _ → itb.QuotStep) <$> itb.step := by
  have he := h
  simp only [IterM.Equiv, BundledIterM.ofIterM, BundledIterM.Equiv, BundledIterM.step,
    ] at h
  simp only [← HetT.comp_map, ← IterStep.mapIterator_comp] at h
  replace h : (IterM.stepAsHetT ita).map IterStep.bundledQuotient =
      (IterM.stepAsHetT itb).map IterStep.bundledQuotient := h
  have h' : ((IterM.stepAsHetT ita).map IterStep.bundledQuotient).pmap
        (fun s hs => Subtype.mk s (step_eq.aux (.refl _) hs)) =
      ((IterM.stepAsHetT itb).map IterStep.bundledQuotient).pmap
        (fun s hs => Subtype.mk s (step_eq.aux he.symm hs)) := by
    congr
    apply step_eq.aux_subtypeMk_congr
    rw [h]
  simp only [HetT.pmap_map] at h'
  replace h' := congrArg (·.map IterM.QuotStep.restrict) h'
  simp only [HetT.map_pmap, IterStep.restrict_bundle (α₂ := α₂),
    IterStep.restrict_bundle (α₂ := α₁)] at h'
  replace h' := congrArg (HetT.prun · (fun x _ => pure x)) h'
  simp only [Equivalence.property_step, HetT.prun_pmap, Equivalence.prun_step, bind_pure_comp] at h'
  simp only [QuotStep.transportAlongEquiv, Functor.map_map, ← h']
  congr
  ext step
  apply Quot.sound
  change _ = IterStep.bundledQuotient (Subtype.val (Exists.choose ?hex))
  let hex := ?hex
  exact hex.choose_spec

theorem IterM.Equiv.lift_step_bind_congr {α₁ α₂ : Type w} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] [MonadLiftT m n] [LawfulMonadLiftT m n]
    [Iterator α₁ m β] [Iterator α₂ m β]
    {ita : IterM (α := α₁) m β} {itb : IterM (α := α₂) m β} (h : IterM.Equiv ita itb)
    {f : _ → n γ} {g : _ → n γ}
    (hfg : ∀ s₁ s₂, s₁.1.bundledQuotient = s₂.1.bundledQuotient → f s₁ = g s₂) :
    ((ita.step : n _) >>= f) = ((itb.step : n _) >>= g) := by
  let flift : ita.QuotStep → n γ := by
    refine Quot.lift ?_ ?_
    · exact f
    · intro s s' h''
      have hs := (IterM.Equiv.exists_step_of_step h s)
      rw [hfg s hs.choose hs.choose_spec, hfg s' hs.choose (h'' ▸ hs.choose_spec)]
  have hf : f = flift ∘ Quot.mk _ := rfl
  let glift : itb.QuotStep → n γ := by
    refine Quot.lift ?_ ?_
    · exact g
    · intro s s' h''
      have hs := (IterM.Equiv.exists_step_of_step h.symm s)
      rw [← hfg hs.choose s hs.choose_spec.symm, ← hfg hs.choose s' (h'' ▸ hs.choose_spec.symm)]
  have hg : g = glift ∘ Quot.mk _ := rfl
  rw [hf, hg, bind_comp_eq_map_bind, bind_comp_eq_map_bind]
  have := congrArg (fun x => liftM (n := n) x) (step_eq h)
  simp only [liftM_map, Functor.map_map] at this
  simp only [this, map_eq_pure_bind, bind_assoc]
  apply bind_congr
  intro step
  simp only [QuotStep.transportAlongEquiv, pure_bind, flift, glift]
  have hex := exists_step_of_step h.symm step
  exact hfg hex.choose step hex.choose_spec.symm

theorem IterM.Equiv.liftInner_stepAsHetT_pbind_congr [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n]
    [MonadLiftT m n] [LawfulMonadLiftT m n] [Iterator α₁ m β] [Iterator α₂ m β]
    {ita : IterM (α := α₁) m β} {itb : IterM (α := α₂) m β}
    {f : (_ : _) → _ → HetT n γ} {g : (_ : _) → _ → HetT n γ} (h : IterM.Equiv ita itb)
    (hfg : ∀ sa hsa sb hsb, sa.bundledQuotient = sb.bundledQuotient → f sa hsa = g sb hsb) :
    ((IterM.stepAsHetT ita).liftInner n).pbind f =
      ((IterM.stepAsHetT itb).liftInner n).pbind g := by
  simp only [HetT.ext_iff, HetT.prun_pbind, HetT.property_liftInner, Equivalence.property_step,
    Equivalence.prun_liftInner_step, HetT.property_pbind]
  refine ⟨?_, ?_⟩
  · ext c
    constructor
    · rintro ⟨s₁, hs₁, hf⟩
      rcases IterM.Equiv.exists_step_of_step h ⟨s₁, hs₁⟩ with ⟨s₂, h'⟩
      exact ⟨s₂.1, s₂.2, (hfg s₁ hs₁ s₂.1 s₂.2 h') ▸ hf⟩
    · rintro ⟨s₁, hs₁, hf⟩
      rcases IterM.Equiv.exists_step_of_step h.symm ⟨s₁, hs₁⟩ with ⟨s₂, h'⟩
      exact ⟨s₂.1, s₂.2, (hfg s₂.1 s₂.2 s₁ hs₁ h'.symm) ▸ hf⟩
  · intro γ l
    apply lift_step_bind_congr h
    intro s₁ s₂ h
    simp only [hfg s₁.1 s₁.2 s₂.1 s₂.2 h]

theorem IterM.Equiv.liftInner_stepAsHetT_bind_congr [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] [MonadLiftT m n] [LawfulMonadLiftT m n] [Iterator α₁ m β]
    [Iterator α₂ m β] {ita : IterM (α := α₁) m β} {itb : IterM (α := α₂) m β}
    {f : (_ : _) → HetT n γ} {g : (_ : _) → HetT n γ} (h : IterM.Equiv ita itb)
    (hfg : ∀ sa (_ : (IterM.stepAsHetT ita).Property sa) sb (_ : (IterM.stepAsHetT itb).Property sb),
        sa.bundledQuotient = sb.bundledQuotient → f sa = g sb) :
    ((IterM.stepAsHetT ita).liftInner n).bind f = ((IterM.stepAsHetT itb).liftInner n).bind g := by
  simp only [HetT.bind_eq_pbind, HetT.property_liftInner, Equivalence.property_step]
  apply liftInner_stepAsHetT_pbind_congr h
  exact hfg

end Std.Iterators
