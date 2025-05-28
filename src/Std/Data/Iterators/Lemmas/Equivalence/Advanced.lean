/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Std.Data.Iterators.Lemmas.Equivalence.Basic

namespace Std.Iterators

def IterStep.bundle [Iterator α m β] [Monad m] [LawfulMonad m]
    (step : IterStep (IterM (α := α) m β) β) :
    IterStep (Quot (ItEquiv m β)) β :=
  step.mapIterator (Quot.mk (ItEquiv m β) ∘ BundledIterM.ofIterM)

def IterM.QuotStep [Iterator α m β] [Monad m] [LawfulMonad m]
    (it : IterM (α := α) m β) :=
  Quot (fun (s₁ s₂ : it.Step) => s₁.1.bundle = s₂.1.bundle)

def IterM.QuotStep.bundle [Iterator α m β] [Monad m] [LawfulMonad m]
    {it : IterM (α := α) m β} : it.QuotStep → IterStep (Quot (ItEquiv m β)) β :=
  Quot.lift (fun s => s.1.bundle) (by intro s t; exact id)

theorem bind_comp_aux {m} [Monad m] [LawfulMonad m] {f : α → β} {g : β → m γ} {x : m α} :
    x >>= (g ∘ f) = (f <$> x) >>= g := by
  simp only [bind_map_left]; rfl

theorem exists_equiv_step [Iterator α₁ m β] [Iterator α₂ m β] [Monad m] [LawfulMonad m]
    {ita : IterM (α := α₁) m β} {itb : IterM (α := α₂) m β}
    (h : HItEquivM ita itb) (s : ita.Step) :
    ∃ s' : itb.Step, s.1.bundle = s'.1.bundle := by
  rw [HItEquivM, ItEquiv] at h
  replace h := congrArg HetT.Property h
  simp only [BundledIterM.ofIterM, BundledIterM.step', funext_iff] at h
  simp only [HetT.property_map] at h
  specialize h s.1.bundle
  rw [eq_iff_iff] at h
  replace h := h.1 ⟨s.1, ?_, s.2⟩
  · rcases h with ⟨s', hs'⟩
    refine ⟨⟨s', hs'.2⟩, hs'.1.symm⟩
  · rfl

open Classical in
noncomputable def IterM.QuotStep.uniqueMap [Iterator α₁ m β] [Iterator α₂ m β] [Monad m] [LawfulMonad m]
    {ita : IterM (α := α₁) m β} {itb : IterM (α := α₂) m β}
    (h : HItEquivM ita itb) : ita.QuotStep → itb.QuotStep := by
  refine Quot.lift ?_ ?_
  · intro s₁
    have := exists_equiv_step h s₁
    exact Quot.mk _ this.choose
  · intro s₁ s₁' hs
    simp
    apply Quot.sound
    have hs₁ := (exists_equiv_step h s₁).choose_spec
    have hs₁' := (exists_equiv_step h s₁').choose_spec
    rw [← hs₁, ← hs₁', hs]

theorem HItEquivM.test {α₁ : Type w} {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    [Iterator α₁ m β] {ita : IterM (α := α₁) m β} {s} :
    (ita.step'.map IterStep.bundle).Property s → ∃ s' : ita.Step, s = s'.1.bundle := by
  simp only [HetT.property_map, forall_exists_index, and_imp]
  rintro s rfl hs
  exact ⟨⟨s, hs⟩, rfl⟩

theorem HItEquivM.test' {α₁ α₂ : Type w} {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    [Iterator α₁ m β] [Iterator α₂ m β]
    {ita : IterM (α := α₁) m β} {itb : IterM (α := α₂) m β} (h : HItEquivM ita itb) {s} :
    (ita.step'.map IterStep.bundle).Property s → ∃ s' : itb.Step, s = s'.1.bundle := by
  intro h
  replace h := test h
  rcases h with ⟨sa, rfl⟩
  rcases exists_equiv_step h sa with ⟨sb, hsb⟩
  exact ⟨sb, hsb⟩

private theorem HItEquivM.step_eq.aux {α : Type u} {P Q R : α → Prop} {h₁ : ∀ a, P a → R a}
    {h₂ : ∀ a, Q a → R a} (h : P = Q) :
    HEq (fun (a : α) (ha : P a) => Subtype.mk a (h₁ a ha))
      (fun (a : α) (ha : Q a) => Subtype.mk a (h₂ a ha)) := by
  cases h
  simp

noncomputable def IterM.QuotStep.restrict [Iterator α m β] [Monad m] [LawfulMonad m]
    {it : IterM (α := α) m β}
    (step : { s : IterStep (Quot (ItEquiv m β)) β // ∃ s' : it.Step, s = s'.1.bundle }) :
    it.QuotStep :=
  Quot.mk _ step.2.choose

theorem IterStep.restrict_bundle [Iterator α₁ m β] [Iterator α₂ m β] [Monad m] [LawfulMonad m]
    {ita : IterM (α := α₁) m β} {step : IterStep (IterM (α := α₂) m β) β}
    {h : ∃ s : ita.Step, step.bundle = s.1.bundle} :
    IterM.QuotStep.restrict ⟨step.bundle, h⟩ = Quot.mk _ h.choose := by
  rfl

theorem HItEquivM.step_eq {α₁ α₂ : Type w} {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    [Iterator α₁ m β] [Iterator α₂ m β]
    {ita : IterM (α := α₁) m β} {itb : IterM (α := α₂) m β} (h : HItEquivM ita itb) :
    (Quot.mk _ : _ → ita.QuotStep) <$> ita.step =
      IterM.QuotStep.uniqueMap h.symm <$> (Quot.mk _ : _ → itb.QuotStep) <$> itb.step := by
  have he := h
  simp only [HItEquivM, BundledIterM.ofIterM, ItEquiv, BundledIterM.step'] at h
  replace h : ita.step'.map IterStep.bundle = itb.step'.map IterStep.bundle := h
  have h' : (ita.step'.map IterStep.bundle).pmap (fun s hs => Subtype.mk s (HItEquivM.test hs)) =
      (itb.step'.map IterStep.bundle).pmap (fun s hs => Subtype.mk s (HItEquivM.test' he.symm hs)) := by
    congr
    apply step_eq.aux
    rw [h]
  simp only [HetT.pmap_map] at h'
  replace h' := congrArg (·.map IterM.QuotStep.restrict) h'
  simp only [HetT.map_pmap, IterStep.restrict_bundle (α₂ := α₂),
    IterStep.restrict_bundle (α₂ := α₁)] at h'
  replace h' := congrArg (HetT.run · (fun x _ => pure x)) h'
  simp [HetT.pmap, IterM.step'] at h'
  simp [IterM.QuotStep.uniqueMap, ← h']
  congr
  ext step
  apply Quot.sound
  change _ = IterStep.bundle (Subtype.val (Exists.choose ?hex))
  let hex := ?hex
  exact hex.choose_spec

theorem HItEquivM.step_congr {α₁ α₂ : Type w} {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    [Iterator α₁ m β] [Iterator α₂ m β]
    {ita : IterM (α := α₁) m β} {itb : IterM (α := α₂) m β} (h : HItEquivM ita itb)
    {f : _ → m γ} {g : _ → m γ}
    (hfg : ∀ s₁ s₂, s₁.1.bundle = s₂.1.bundle → f s₁ = g s₂) :
    (ita.step >>= f) = (itb.step >>= g) := by
  let flift : ita.QuotStep → m γ := by
    refine Quot.lift ?_ ?_
    · exact f
    · intro s₁ s₁' h''
      have hs₁ := (exists_equiv_step h s₁)
      have hs₁' := (exists_equiv_step h s₁')
      let s₂ := hs₁.choose
      have hfg₁ := hfg s₁ s₂ hs₁.choose_spec
      have hfg₂ := hfg s₁' s₂ (h'' ▸ hs₁.choose_spec)
      rw [hfg₁, hfg₂]
  have hf : f = flift ∘ Quot.mk _ := rfl
  let glift : itb.QuotStep → m γ := by
    refine Quot.lift ?_ ?_
    · exact g
    · intro s₁ s₁' h''
      replace h : HItEquivM itb ita := h.symm
      have hs₁ := (exists_equiv_step h s₁)
      have hs₁' := (exists_equiv_step h s₁')
      let s₂ := hs₁.choose
      have hfg₁ := hfg s₂ s₁ hs₁.choose_spec.symm
      have hfg₂ := hfg s₂ s₁' (h'' ▸ hs₁.choose_spec.symm)
      rw [← hfg₁, ← hfg₂]
  have hg : g = glift ∘ Quot.mk _ := rfl
  rw [hf, hg, bind_comp_aux, bind_comp_aux]
  simp only [step_eq h, map_eq_pure_bind, bind_assoc]
  apply bind_congr
  intro step
  simp [IterM.QuotStep.uniqueMap, flift, glift, Quot.liftBeta]
  change f (Exists.choose ?hex) = _; let hex := ?hex
  exact hfg hex.choose step hex.choose_spec.symm
