/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Lemmas.Consumers.Monadic.Collect
public import Init.Data.Iterators.Consumers.Monadic.Loop
import all Init.Data.Iterators.Consumers.Monadic.Loop

public section

namespace Std
open Std.Iterators

theorem IterM.DefaultConsumers.forIn'_eq_match_step {α β : Type w} {m : Type w → Type w'}
    [Iterator α m β] {n : Type x → Type x'} [Monad n] [LawfulMonad n]
    {lift : ∀ γ δ, (γ → n δ) → m γ → n δ} {γ : Type x}
    {it : IterM (α := α) m β} {init : γ}
    {P hP}
    (PlausibleForInStep : β → γ → ForInStep γ → Prop)
    {f : (b : β) → P b → (c : γ) → n (Subtype (PlausibleForInStep b c))}
    (wf : IteratorLoop.WellFounded α m PlausibleForInStep) :
    IterM.DefaultConsumers.forIn' lift γ PlausibleForInStep it init P hP f =
      (lift _ _ · it.step) (fun s =>
          match s.inflate with
          | .yield it' out h => do
            match ← f out (hP _ <| .direct ⟨_, h⟩) init with
            | ⟨.yield c, _⟩ =>
              IterM.DefaultConsumers.forIn' lift _ PlausibleForInStep it' c P
                (fun _ h' => hP _ <| .indirect ⟨_, rfl, h⟩ h') f
            | ⟨.done c, _⟩ => return c
          | .skip it' h =>
            IterM.DefaultConsumers.forIn' lift _ PlausibleForInStep it' init P
              (fun _ h' => hP _ <| .indirect ⟨_, rfl, h⟩ h') f
          | .done _ => return init) := by
  haveI : Nonempty γ := ⟨init⟩
  rw [forIn', WellFounded.extrinsicFix₃_eq_apply]
  · congr; ext step
    cases step.inflate using PlausibleIterStep.casesOn
    · simp only
      apply bind_congr; intro step
      split <;> simp [forIn']
    · simp [forIn']
    · simp
  · apply InvImage.wf
    exact wf

theorem IterM.DefaultConsumers.forIn'_eq_wf {m : Type w → Type w'} {α : Type w} {β : Type w}
    [Iterator α m β]
    {n : Type x → Type x'} [Monad n] [LawfulMonad n]
    {lift : ∀ γ δ, (γ → n δ) → m γ → n δ} {γ : Type x}
    (Pl : β → γ → ForInStep γ → Prop)
    (wf : IteratorLoop.WellFounded α m Pl)
    {it : IterM (α := α) m β} {init : γ}
    {P : β → Prop} {hP : ∀ b, it.IsPlausibleIndirectOutput b → P b}
    (f : (b : β) → P b → (c : γ) → n (Subtype (Pl b c))) :
    forIn' lift γ Pl it init P hP f =
      forIn'.wf lift γ Pl wf it init P hP f := by
  haveI : Nonempty γ := ⟨init⟩
  rw [forIn', WellFounded.extrinsicFix₃_eq_fix]; rotate_left
  · apply InvImage.wf
    exact wf
  · fun_induction forIn'.wf lift γ Pl wf it init P hP f
    rename_i ihy ihs
    rw [WellFounded.fix_eq]
    congr 1; ext step
    cases step.inflate using PlausibleIterStep.casesOn
    · apply bind_congr; intro forInStep
      match forInStep with
      | ⟨.yield c, h⟩ => simp (discharger := assumption) [ihy]
      | ⟨.done c, h⟩ => simp
    · simp (discharger := assumption) [ihs]
    · simp

theorem IterM.DefaultConsumers.forIn'_eq_wf_of_finite {m : Type w → Type w'} {α : Type w}
    {β : Type w} [Iterator α m β] [Finite α m]
    {n : Type x → Type x'} [Monad n] [LawfulMonad n]
    {lift : ∀ γ δ, (γ → n δ) → m γ → n δ} {γ : Type x}
    {it : IterM (α := α) m β} {init : γ}
    {P : β → Prop} {hP : ∀ b, it.IsPlausibleIndirectOutput b → P b}
    (f : (b : β) → P b → (c : γ) → n (Subtype (fun _ => True))) :
    forIn' lift γ (fun _ _ _ => True) it init P hP f =
      forIn'.wf lift γ (fun _ _ _ => True) IteratorLoop.wellFounded_of_finite it init P hP f := by
  apply forIn'_eq_wf

theorem IterM.forIn'_eq {α β : Type w} {m : Type w → Type w'} [Iterator α m β] [Finite α m]
    {n : Type w → Type w''} [Monad m] [Monad n] [LawfulMonad n] [IteratorLoop α m n]
    [hl : LawfulIteratorLoop α m n]
    [MonadLiftT m n] [LawfulMonadLiftT m n] {γ : Type w} {it : IterM (α := α) m β} {init : γ}
    {f : (b : β) → it.IsPlausibleIndirectOutput b → γ → n (ForInStep γ)} :
    letI : ForIn' n (IterM (α := α) m β) β _ := IterM.instForIn'
    ForIn'.forIn' (α := β) (m := n) it init f = IterM.DefaultConsumers.forIn' (n := n)
        (fun _ _ f x => monadLift x >>= f) γ (fun _ _ _ => True) it init _ (fun _ => id) (return ⟨← f · · ·, trivial⟩) := by
  simp only [instForIn', ForIn'.forIn', IteratorLoop.finiteForIn']
  have : f = (Subtype.val <$> (⟨·, trivial⟩) <$> f · · ·) := by simp
  rw [this, hl.lawful (fun _ _ f x => monadLift x >>= f) (wf := IteratorLoop.wellFounded_of_finite)]
  simp [IteratorLoop.defaultImplementation]

theorem IterM.forIn_eq {α β : Type w} {m : Type w → Type w'} [Iterator α m β] [Finite α m]
    {n : Type w → Type w''} [Monad m] [Monad n] [LawfulMonad n] [IteratorLoop α m n]
    [hl : LawfulIteratorLoop α m n]
    [MonadLiftT m n] [LawfulMonadLiftT m n] {γ : Type w} {it : IterM (α := α) m β} {init : γ}
    {f : β → γ → n (ForInStep γ)} :
    ForIn.forIn it init f = IterM.DefaultConsumers.forIn' (n := n)
        (fun _ _ f x => monadLift x >>= f) γ (fun _ _ _ => True) it init _ (fun _ => id)
        (fun out _ acc => return ⟨← f out acc, trivial⟩) := by
  simp only [ForIn.forIn, forIn'_eq]

@[congr] theorem IterM.forIn'_congr {α β : Type w} {m : Type w → Type w'}
    {n : Type w → Type w''} [Monad n] [Monad m]
    [Iterator α m β] [IteratorLoop α m n] [MonadLiftT m n]
    {ita itb : IterM (α := α) m β} (w : ita = itb)
    {b b' : γ} (hb : b = b')
    {f : (a' : β) → _ → γ → n (ForInStep γ)}
    {g : (a' : β) → _ → γ → n (ForInStep γ)}
    (h : ∀ a m b, f a (by simpa [w] using m) b = g a m b) :
    letI : ForIn' n (IterM (α := α) m β) β _ := IterM.instForIn'
    forIn' ita b f = forIn' itb b' g := by
  subst_eqs
  simp only [← funext_iff] at h
  rw [← h]
  rfl

@[congr] theorem IterM.forIn_congr {α β : Type w} {m : Type w → Type w'}
    {n : Type w → Type w''} [Monad n] [Monad m]
    [Iterator α m β] [IteratorLoop α m n] [MonadLiftT m n]
    {ita itb : IterM (α := α) m β} (w : ita = itb)
    {b b' : γ} (hb : b = b')
    {f : (a' : β) → γ → n (ForInStep γ)}
    {g : (a' : β) → γ → n (ForInStep γ)}
    (h : ∀ a b, f a b = g a b) :
    forIn ita b f = forIn itb b' g := by
  subst_eqs
  simp only [← funext_iff] at h
  rw [← h]

theorem IterM.DefaultConsumers.forIn'_eq_forIn' {m : Type w → Type w'} {α : Type w} {β : Type w}
    [Iterator α m β]
    {n : Type x → Type x'} [Monad n] [LawfulMonad n]
    {lift : ∀ γ δ, (γ → n δ) → m γ → n δ} {γ : Type x}
    {it : IterM (α := α) m β} {init : γ}
    {P : β → Prop} {hP : ∀ b, it.IsPlausibleIndirectOutput b → P b}
    {Q : β → Prop} {hQ : ∀ b, it.IsPlausibleIndirectOutput b → Q b}
    (Pl : β → γ → ForInStep γ → Prop)
    {f : (b : β) → P b → (c : γ) → n (Subtype (Pl b c))}
    {g : (b : β) → Q b → (c : γ) → n (Subtype (Pl b c))}
    (wf : IteratorLoop.WellFounded α m Pl)
    (hfg : ∀ b c, (hPb : P b) → (hQb : Q b) → f b hPb c = g b hQb c) :
    IterM.DefaultConsumers.forIn' lift γ Pl it init P hP f =
      IterM.DefaultConsumers.forIn' lift γ Pl it init Q hQ g := by
  rw [forIn'_eq_match_step Pl wf, forIn'_eq_match_step Pl wf]
  congr; ext step
  split
  · congr
    · apply hfg
    · ext forInStep
      match forInStep with
      | ⟨.yield _, h⟩ => apply IterM.DefaultConsumers.forIn'_eq_forIn' <;> assumption
      | ⟨.done _, h⟩ => rfl
  · apply IterM.DefaultConsumers.forIn'_eq_forIn' <;> assumption
  · rfl
termination_by IteratorLoop.WithWF.mk it init (hwf := wf)
decreasing_by
  · exact Or.inl ⟨_, ‹_›, ‹_›⟩
  · exact Or.inr ⟨‹_›, rfl⟩

theorem IterM.forIn'_eq_match_step {α β : Type w} {m : Type w → Type w'} [Iterator α m β]
    [Finite α m] {n : Type w → Type w''} [Monad m] [Monad n] [LawfulMonad n]
    [IteratorLoop α m n] [LawfulIteratorLoop α m n]
    [MonadLiftT m n] [LawfulMonadLiftT m n] {γ : Type w} {it : IterM (α := α) m β} {init : γ}
    {f : (out : β) → _ → γ → n (ForInStep γ)} :
    letI : ForIn' n (IterM (α := α) m β) β _ := IterM.instForIn'
    ForIn'.forIn' it init f = (do
      match (← it.step).inflate with
      | .yield it' out h =>
        match ← f out (.direct ⟨_, h⟩) init with
        | .yield c =>
          ForIn'.forIn' it' c
            fun out h'' acc => f out (.indirect ⟨_, rfl, h⟩ h'') acc
        | .done c => return c
      | .skip it' h =>
        ForIn'.forIn' it' init
          fun out h' acc => f out (.indirect ⟨_, rfl, h⟩ h') acc
      | .done _ => return init) := by
  rw [IterM.forIn'_eq, DefaultConsumers.forIn'_eq_match_step]
  · apply bind_congr; intro step
    cases step.inflate using PlausibleIterStep.casesOn
    · simp only [bind_assoc]
      apply bind_congr
      intro forInStep
      cases forInStep
      · simp
      · simp only [forIn'_eq, pure_bind]
        exact DefaultConsumers.forIn'_eq_forIn' (α := α) (m := m) (n := n) _
          IteratorLoop.wellFounded_of_finite (by simp)
    · simp only [forIn'_eq]
      exact DefaultConsumers.forIn'_eq_forIn' (α := α) (m := m) (n := n) _
          IteratorLoop.wellFounded_of_finite (by simp)
    · simp
  · exact IteratorLoop.wellFounded_of_finite

theorem IterM.forIn_eq_match_step {α β : Type w} {m : Type w → Type w'} [Iterator α m β]
    [Finite α m] {n : Type w → Type w''} [Monad m] [Monad n] [LawfulMonad n]
    [IteratorLoop α m n] [LawfulIteratorLoop α m n]
    [MonadLiftT m n] [LawfulMonadLiftT m n] {γ : Type w} {it : IterM (α := α) m β} {init : γ}
    {f : β → γ → n (ForInStep γ)} :
    ForIn.forIn it init f = (do
      match (← it.step).inflate with
      | .yield it' out _ =>
        match ← f out init with
        | .yield c => ForIn.forIn it' c f
        | .done c => return c
      | .skip it' _ => ForIn.forIn it' init f
      | .done _ => return init) := by
  simp only [forIn]
  exact forIn'_eq_match_step

theorem IterM.forIn_toList {α β : Type w} [Monad m] [LawfulMonad m] [Iterator α Id β]
    [Finite α Id] [IteratorLoop α Id m] [LawfulIteratorLoop α Id m]
    {it : IterM (α := α) Id β} {f : β → γ → m (ForInStep γ)} {init : γ} :
    ForIn.forIn it.toList.run init f = ForIn.forIn it init f := by
  rw [List.forIn_eq_foldlM]
  induction it using IterM.inductSteps generalizing init with | step it ihy ihs
  rw [forIn_eq_match_step, IterM.toList_eq_match_step]
  simp only [map_eq_pure_bind, Id.run_bind, liftM, monadLift, pure_bind]
  cases it.step.run.inflate using PlausibleIterStep.casesOn
  · rename_i it' out h
    simp only [List.foldlM_cons, bind_pure_comp, map_bind, Id.run_map]
    apply bind_congr
    intro forInStep
    cases forInStep
    · induction it'.toList.run <;> simp [*]
    · simp only [ForIn.forIn] at ihy
      simp [ihy h]
  · rename_i it' h
    simp only [bind_pure_comp]
    rw [ihs h]
  · simp

theorem IterM.forIn_toArray {α β : Type w} [Monad m] [LawfulMonad m] [Iterator α Id β]
    [Finite α Id] [IteratorLoop α Id m] [LawfulIteratorLoop α Id m]
    {it : IterM (α := α) Id β} {f : β → γ → m (ForInStep γ)} {init : γ} :
    ForIn.forIn it.toArray.run init f = ForIn.forIn it init f := by
  simp [← toArray_toList, forIn_toList]

theorem IterM.forM_eq_forIn {α β : Type w} {m : Type w → Type w'} [Iterator α m β]
    [Finite α m] {n : Type w → Type w''} [Monad m] [Monad n] [LawfulMonad n]
    [IteratorLoop α m n] [LawfulIteratorLoop α m n]
    [MonadLiftT m n] {it : IterM (α := α) m β}
    {f : β → n PUnit} :
    ForM.forM it f = ForIn.forIn it PUnit.unit (fun out _ => do f out; return .yield .unit) :=
  rfl

theorem IterM.forM_eq_match_step {α β : Type w} {m : Type w → Type w'} [Iterator α m β]
    [Finite α m] {n : Type w → Type w''} [Monad m] [Monad n] [LawfulMonad n]
    [IteratorLoop α m n] [LawfulIteratorLoop α m n]
    [MonadLiftT m n] [LawfulMonadLiftT m n] {it : IterM (α := α) m β}
    {f : β → n PUnit} :
    ForM.forM it f = (do
      match (← it.step).inflate with
      | .yield it' out _ =>
        f out
        ForM.forM it' f
      | .skip it' _ => ForM.forM it' f
      | .done _ => return) := by
  rw [forM_eq_forIn, forIn_eq_match_step]
  apply bind_congr
  intro step
  cases step.inflate using PlausibleIterStep.casesOn <;> simp [forM_eq_forIn]

theorem IterM.foldM_eq_forIn {α β γ : Type w} {m : Type w → Type w'} [Iterator α m β] [Finite α m]
    {n : Type w → Type w''} [Monad n] [IteratorLoop α m n] [MonadLiftT m n] {f : γ → β → n γ}
    {init : γ} {it : IterM (α := α) m β} :
    it.foldM (init := init) f = ForIn.forIn it init (fun x acc => ForInStep.yield <$> f acc x) :=
  (rfl)

theorem IterM.forIn_yield_eq_foldM {α β γ δ : Type w} {m : Type w → Type w'} [Iterator α m β]
    [Finite α m] {n : Type w → Type w''} [Monad m] [Monad n] [LawfulMonad n] [IteratorLoop α m n]
    [LawfulIteratorLoop α m n] [MonadLiftT m n] {f : β → γ → n δ} {g : β → γ → δ → γ} {init : γ}
    {it : IterM (α := α) m β} :
    ForIn.forIn it init (fun c b => (fun d => .yield (g c b d)) <$> f c b) =
      it.foldM (fun b c => g c b <$> f c b) init := by
  simp [IterM.foldM_eq_forIn]

theorem IterM.foldM_eq_match_step {α β γ : Type w} {m : Type w → Type w'} [Iterator α m β] [Finite α m]
    {n : Type w → Type w''} [Monad m] [Monad n] [LawfulMonad n] [IteratorLoop α m n]
    [LawfulIteratorLoop α m n] [MonadLiftT m n] [LawfulMonadLiftT m n]
    {f : γ → β → n γ} {init : γ} {it : IterM (α := α) m β} :
    it.foldM (init := init) f = (do
      match (← it.step).inflate with
      | .yield it' out _ => it'.foldM (init := ← f init out) f
      | .skip it' _ => it'.foldM (init := init) f
      | .done _ => return init) := by
  rw [IterM.foldM_eq_forIn, IterM.forIn_eq_match_step]
  apply bind_congr
  intro step
  cases step.inflate using PlausibleIterStep.casesOn <;> simp [foldM_eq_forIn]

theorem IterM.fold_eq_forIn {α β γ : Type w} {m : Type w → Type w'} [Iterator α m β]
    [Finite α m] [Monad m]
    [IteratorLoop α m m] {f : γ → β → γ} {init : γ} {it : IterM (α := α) m β} :
    it.fold (init := init) f =
      ForIn.forIn (m := m) it init (fun x acc => pure (ForInStep.yield (f acc x))) := by
  rfl

theorem IterM.fold_eq_foldM {α β γ : Type w} {m : Type w → Type w'} [Iterator α m β]
    [Finite α m] [Monad m] [LawfulMonad m] [IteratorLoop α m m] {f : γ → β → γ} {init : γ}
    {it : IterM (α := α) m β} :
    it.fold (init := init) f = it.foldM (init := init) (pure <| f · ·) := by
  simp [foldM_eq_forIn, fold_eq_forIn]

@[simp]
theorem IterM.forIn_pure_yield_eq_fold {α β γ : Type w} {m : Type w → Type w'} [Iterator α m β]
    [Finite α m] [Monad m] [LawfulMonad m] [IteratorLoop α m m]
    [LawfulIteratorLoop α m m] {f : β → γ → γ} {init : γ}
    {it : IterM (α := α) m β} :
    ForIn.forIn it init (fun c b => pure (.yield (f c b))) =
      it.fold (fun b c => f c b) init := by
  simp [IterM.fold_eq_forIn]

theorem IterM.fold_eq_match_step {α β γ : Type w} {m : Type w → Type w'} [Iterator α m β] [Finite α m]
    [Monad m] [LawfulMonad m] [IteratorLoop α m m] [LawfulIteratorLoop α m m]
    {f : γ → β → γ} {init : γ} {it : IterM (α := α) m β} :
    it.fold (init := init) f = (do
      match (← it.step).inflate with
      | .yield it' out _ => it'.fold (init := f init out) f
      | .skip it' _ => it'.fold (init := init) f
      | .done _ => return init) := by
  rw [fold_eq_foldM, foldM_eq_match_step]
  simp only [fold_eq_foldM]
  apply bind_congr
  intro step
  cases step.inflate using PlausibleIterStep.casesOn <;> simp

-- The argument `f : γ₁ → γ₂` is intentionally explicit, as it is sometimes not found by unification.
theorem IterM.fold_hom {m : Type w → Type w'} [Iterator α m β] [Finite α m]
    [Monad m] [LawfulMonad m] [IteratorLoop α m m] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β}
    (f : γ₁ → γ₂) {g₁ : γ₁ → β → γ₁} {g₂ : γ₂ → β → γ₂} {init : γ₁}
    (H : ∀ x y, g₂ (f x) y = f (g₁ x y)) :
    it.fold g₂ (f init) = f <$> (it.fold g₁ init) := by
  induction it using IterM.inductSteps generalizing init with | step it ihy ihs =>
  rw [fold_eq_match_step, fold_eq_match_step, map_eq_pure_bind, bind_assoc]
  apply bind_congr
  intro step
  rw [bind_pure_comp]
  split
  · rw [H, ihy ‹_›]
  · rw [ihs ‹_›]
  · simp

theorem IterM.toList_eq_fold {α β : Type w} {m : Type w → Type w'} [Iterator α m β]
    [Finite α m] [Monad m] [LawfulMonad m] [IteratorLoop α m m] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} :
    it.toList = it.fold (init := []) (fun l out => l ++ [out]) := by
  suffices h : ∀ l' : List β, (l' ++ ·) <$> it.toList =
      it.fold (init := l') (fun l out => l ++ [out]) by
    specialize h []
    simpa using h
  induction it using IterM.inductSteps with | step it ihy ihs
  intro l'
  rw [IterM.toList_eq_match_step, IterM.fold_eq_match_step]
  simp only [map_eq_pure_bind, bind_assoc]
  apply bind_congr
  intro step
  cases step.inflate using PlausibleIterStep.casesOn
  · rename_i it' out h
    specialize ihy h (l' ++ [out])
    simpa using ihy
  · rename_i it' h
    simp [ihs h]
  · simp

theorem IterM.toArray_eq_fold {α β : Type w} {m : Type w → Type w'} [Iterator α m β]
    [Finite α m] [Monad m] [LawfulMonad m] [IteratorLoop α m m] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} :
    it.toArray = it.fold (init := #[]) (fun xs out => xs.push out) := by
  simp only [← toArray_toList, toList_eq_fold]
  rw [← fold_hom]
  simp

theorem IterM.foldlM_toList {α β : Type w} [Monad m] [LawfulMonad m] [Iterator α Id β]
    [Finite α Id] [IteratorLoop α Id m] [LawfulIteratorLoop α Id m]
    {it : IterM (α := α) Id β} {f : γ → β → m γ} {init : γ} :
    it.toList.run.foldlM f init = it.foldM f init := by
  simp [foldM_eq_forIn, ← forIn_toList]

theorem IterM.foldlM_toArray {α β : Type w} [Monad m] [LawfulMonad m] [Iterator α Id β]
    [Finite α Id] [IteratorLoop α Id m] [LawfulIteratorLoop α Id m]
    {it : IterM (α := α) Id β} {f : γ → β → m γ} {init : γ} :
    it.toArray.run.foldlM f init = it.foldM f init := by
  simp [← toArray_toList, foldlM_toList]

theorem IterM.foldl_toList {α β : Type w} [Monad m] [LawfulMonad m] [Iterator α m β]
    [Finite α m] [IteratorLoop α m m] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} {f : γ → β → γ} {init : γ} :
    (·.foldl f init) <$> it.toList = it.fold f init := by
  induction it using IterM.inductSteps generalizing init with | step it ihy ihs
  rw [toList_eq_match_step, fold_eq_match_step]
  simp only [bind_pure_comp, map_bind]
  apply bind_congr; intro step
  cases step.inflate using PlausibleIterStep.casesOn
  · simp [ihy ‹_›]
  · simp [ihs ‹_›]
  · simp

theorem IterM.foldl_toArray {α β : Type w} [Monad m] [LawfulMonad m] [Iterator α m β]
    [Finite α m] [IteratorLoop α m m] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} {f : γ → β → γ} {init : γ} :
    (·.foldl f init) <$> it.toArray = it.fold f init := by
  simp only [← toArray_toList, Functor.map_map, List.foldl_toArray, foldl_toList]

theorem IterM.drain_eq_fold {α β : Type w} {m : Type w → Type w'} [Iterator α m β] [Finite α m]
    [Monad m] [IteratorLoop α m m] {it : IterM (α := α) m β} :
    it.drain = it.fold (init := PUnit.unit) (fun _ _ => .unit) :=
  (rfl)

theorem IterM.drain_eq_foldM {α β : Type w} {m : Type w → Type w'} [Iterator α m β] [Finite α m]
    [Monad m] [LawfulMonad m] [IteratorLoop α m m] {it : IterM (α := α) m β} :
    it.drain = it.foldM (init := PUnit.unit) (fun _ _ => pure .unit) := by
  simp [IterM.drain_eq_fold, IterM.fold_eq_foldM]

theorem IterM.drain_eq_forIn {α β : Type w} {m : Type w → Type w'}  [Iterator α m β] [Finite α m]
    [Monad m] [IteratorLoop α m m] {it : IterM (α := α) m β} :
    it.drain = ForIn.forIn (m := m) it PUnit.unit (fun _ _ => pure (ForInStep.yield .unit)) := by
  simp [IterM.drain_eq_fold, IterM.fold_eq_forIn]

theorem IterM.drain_eq_match_step {α β : Type w} {m : Type w → Type w'} [Iterator α m β] [Finite α m]
    [Monad m] [LawfulMonad m] [IteratorLoop α m m] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} :
    it.drain = (do
      match (← it.step).inflate with
      | .yield it' _ _ => it'.drain
      | .skip it' _ => it'.drain
      | .done _ => return .unit) := by
  rw [IterM.drain_eq_fold, IterM.fold_eq_match_step]
  simp [IterM.drain_eq_fold]

theorem IterM.drain_eq_map_toList {α β : Type w} {m : Type w → Type w'} [Iterator α m β]
    [Finite α m] [Monad m] [LawfulMonad m] [IteratorLoop α m m] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} :
    it.drain = (fun _ => .unit) <$> it.toList := by
  induction it using IterM.inductSteps with | step it ihy ihs
  rw [IterM.drain_eq_match_step, IterM.toList_eq_match_step]
  simp only [map_eq_pure_bind, bind_assoc]
  apply bind_congr
  intro step
  cases step.inflate using PlausibleIterStep.casesOn
  · rename_i it' out h
    simp [ihy h]
  · rename_i it' h
    simp [ihs h]
  · simp

theorem IterM.drain_eq_map_toListRev {α β : Type w} {m : Type w → Type w'} [Iterator α m β]
    [Finite α m] [Monad m] [LawfulMonad m] [IteratorLoop α m m] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} :
    it.drain = (fun _ => .unit) <$> it.toListRev := by
  simp [IterM.drain_eq_map_toList, IterM.toListRev_eq]

theorem IterM.drain_eq_map_toArray {α β : Type w} {m : Type w → Type w'} [Iterator α m β]
    [Finite α m] [Monad m] [LawfulMonad m] [IteratorLoop α m m] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} :
    it.drain = (fun _ => .unit) <$> it.toList := by
  simp [IterM.drain_eq_map_toList]

theorem IterM.count_eq_fold {α β : Type w} {m : Type w → Type w'} [Iterator α m β]
    [Finite α m] [Monad m] [LawfulMonad m] [IteratorLoop α m m]
    {it : IterM (α := α) m β} :
    it.count = it.fold (init := .up 0) (fun acc _ => .up <| acc.down + 1) :=
  (rfl)

theorem IterM.count_eq_forIn {α β : Type w} {m : Type w → Type w'} [Iterator α m β]
    [Finite α m] [Monad m] [LawfulMonad m] [IteratorLoop α m m]
    {it : IterM (α := α) m β} :
    it.count = ForIn.forIn it (.up 0) (fun _ acc => return .yield (.up (acc.down + 1))) :=
  (rfl)

theorem IterM.count_eq_match_step {α β : Type w} {m : Type w → Type w'} [Iterator α m β]
    [Finite α m] [Monad m] [LawfulMonad m] [IteratorLoop α m m] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} :
    it.count = (do
      match (← it.step).inflate.val with
      | .yield it' _ => return .up ((← it'.count).down + 1)
      | .skip it' => return .up (← it'.count).down
      | .done => return .up 0) := by
  simp only [count_eq_fold]
  have (acc : Nat) (it' : IterM (α := α) m β) :
      it'.fold (init := ULift.up acc) (fun acc _ => .up (acc.down + 1)) =
        (ULift.up <| ·.down + acc) <$>
          it'.fold (init := ULift.up 0) (fun acc _ => .up (acc.down + 1)) := by
    rw [← fold_hom]
    · simp only [Nat.zero_add]; rfl
    · simp only [ULift.up.injEq]; omega
  rw [fold_eq_match_step]
  apply bind_congr; intro step
  cases step.inflate using PlausibleIterStep.casesOn
  · simp only [Nat.zero_add, bind_pure_comp]
    rw [this 1]
  · simp
  · simp

@[simp]
theorem IterM.up_size_toArray_eq_count {α β : Type w} [Iterator α m β] [Finite α m]
    [Monad m] [LawfulMonad m]
    [IteratorLoop α m m] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} :
    (.up <| ·.size) <$> it.toArray = it.count := by
  rw [toArray_eq_fold, count_eq_fold, ← fold_hom]
  · simp only [List.size_toArray, List.length_nil]; rfl
  · simp

@[simp]
theorem IterM.up_length_toList_eq_count {α β : Type w} [Iterator α m β] [Finite α m]
    [Monad m] [LawfulMonad m]
    [IteratorLoop α m m] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} :
    (.up <| ·.length) <$> it.toList = it.count := by
  rw [toList_eq_fold, count_eq_fold, ← fold_hom]
  · simp only [List.length_nil]; rfl
  · simp

@[simp]
theorem IterM.up_length_toListRev_eq_count {α β : Type w} [Iterator α m β] [Finite α m]
    [Monad m] [LawfulMonad m]
    [IteratorLoop α m m] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} :
    (.up <| ·.length) <$> it.toListRev = it.count := by
  simp only [toListRev_eq, Functor.map_map, List.length_reverse, up_length_toList_eq_count]

theorem IterM.anyM_eq_forIn {α β : Type w} {m : Type w → Type w'} [Iterator α m β]
    [Finite α m] [Monad m] [LawfulMonad m] [IteratorLoop α m m] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} {p : β → m (ULift Bool)} :
    it.anyM p = (ForIn.forIn it (.up false) (fun x _ => do
        if (← p x).down then
          return .done (.up true)
        else
          return .yield (.up false))) := by
  rfl

theorem IterM.anyM_eq_match_step {α β : Type w} {m : Type w → Type w'} [Iterator α m β]
    [Finite α m] [Monad m] [LawfulMonad m] [IteratorLoop α m m] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} {p : β → m (ULift Bool)} :
    it.anyM p = (do
      match (← it.step).inflate.val with
      | .yield it' x =>
        if (← p x).down then
          return .up true
        else
          it'.anyM p
      | .skip it' => it'.anyM p
      | .done => return .up false) := by
  rw [anyM_eq_forIn, forIn_eq_match_step]
  simp only [monadLift_self, bind_assoc]
  apply bind_congr; intro step
  cases step.inflate using PlausibleIterStep.casesOn
  · apply bind_congr; intro px
    split
    · simp
    · simp [anyM_eq_forIn]
  · simp [anyM_eq_forIn]
  · simp

theorem IterM.any_eq_anyM {α β : Type w} {m : Type w → Type w'} [Iterator α m β]
    [Finite α m] [Monad m] [LawfulMonad m] [IteratorLoop α m m] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} {p : β → Bool} :
    it.any p = it.anyM (fun x => pure (.up (p x))) := by
  rfl

theorem IterM.anyM_pure {α β : Type w} {m : Type w → Type w'} [Iterator α m β]
    [Finite α m] [Monad m] [LawfulMonad m] [IteratorLoop α m m] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} {p : β → ULift Bool} :
    it.anyM (fun x => pure (p x)) = it.any (fun x => (p x).down) := by
  simp [any_eq_anyM]

theorem IterM.any_eq_match_step {α β : Type w} {m : Type w → Type w'} [Iterator α m β]
    [Finite α m] [Monad m] [LawfulMonad m] [IteratorLoop α m m] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} {p : β → Bool} :
    it.any p = (do
      match (← it.step).inflate.val with
      | .yield it' x =>
        if p x then
          return .up true
        else
          it'.any p
      | .skip it' => it'.any p
      | .done => return .up false) := by
  rw [any_eq_anyM, anyM_eq_match_step]
  apply bind_congr; intro step
  split
  · simp [any_eq_anyM]
  · simp [any_eq_anyM]
  · simp

theorem IterM.any_eq_forIn {α β : Type w} {m : Type w → Type w'} [Iterator α m β]
    [Finite α m] [Monad m] [LawfulMonad m] [IteratorLoop α m m] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} {p : β → Bool} :
    it.any p = (ForIn.forIn it (.up false) (fun x _ => do
        if p x then
          return .done (.up true)
        else
          return .yield (.up false))) := by
  simp [any_eq_anyM, anyM_eq_forIn]

theorem IterM.allM_eq_forIn {α β : Type w} {m : Type w → Type w'} [Iterator α m β]
    [Finite α m] [Monad m] [LawfulMonad m] [IteratorLoop α m m] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} {p : β → m (ULift Bool)} :
    it.allM p = (ForIn.forIn it (.up true) (fun x _ => do
        if (← p x).down then
          return .yield (.up true)
        else
          return .done (.up false))) := by
  rfl

theorem IterM.allM_eq_match_step {α β : Type w} {m : Type w → Type w'} [Iterator α m β]
    [Finite α m] [Monad m] [LawfulMonad m] [IteratorLoop α m m] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} {p : β → m (ULift Bool)} :
    it.allM p = (do
      match (← it.step).inflate.val with
      | .yield it' x =>
        if (← p x).down then
          it'.allM p
        else
          return .up false
      | .skip it' => it'.allM p
      | .done => return .up true) := by
  rw [allM_eq_forIn, forIn_eq_match_step]
  simp only [monadLift_self, bind_assoc]
  apply bind_congr; intro step
  cases step.inflate using PlausibleIterStep.casesOn
  · apply bind_congr; intro px
    split
    · simp [allM_eq_forIn]
    · simp
  · simp [allM_eq_forIn]
  · simp

theorem IterM.all_eq_allM {α β : Type w} {m : Type w → Type w'} [Iterator α m β]
    [Finite α m] [Monad m] [LawfulMonad m] [IteratorLoop α m m] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} {p : β → Bool} :
    it.all p = it.allM (fun x => pure (.up (p x))) := by
  rfl

theorem IterM.allM_pure {α β : Type w} {m : Type w → Type w'} [Iterator α m β]
    [Finite α m] [Monad m] [LawfulMonad m] [IteratorLoop α m m] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} {p : β → ULift Bool} :
    it.allM (fun x => pure (p x)) = it.all (fun x => (p x).down) := by
  simp [all_eq_allM]

theorem IterM.all_eq_match_step {α β : Type w} {m : Type w → Type w'} [Iterator α m β]
    [Finite α m] [Monad m] [LawfulMonad m] [IteratorLoop α m m] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} {p : β → Bool} :
    it.all p = (do
      match (← it.step).inflate.val with
      | .yield it' x =>
        if p x then
          it'.all p
        else
          return .up false
      | .skip it' => it'.all p
      | .done => return .up true) := by
  rw [all_eq_allM, allM_eq_match_step]
  apply bind_congr; intro step
  split
  · simp [all_eq_allM]
  · simp [all_eq_allM]
  · simp

theorem IterM.all_eq_forIn {α β : Type w} {m : Type w → Type w'} [Iterator α m β]
    [Finite α m] [Monad m] [LawfulMonad m] [IteratorLoop α m m] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} {p : β → Bool} :
    it.all p = (ForIn.forIn it (.up true) (fun x _ => do
        if p x then
          return .yield (.up true)
        else
          return .done (.up false))) := by
  simp [all_eq_allM, allM_eq_forIn]

theorem IterM.allM_eq_not_anyM_not {α β : Type w} {m : Type w → Type w'} [Iterator α m β]
    [Finite α m] [Monad m] [LawfulMonad m] [IteratorLoop α m m] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} {p : β → m (ULift Bool)} :
    it.allM p = (fun x => .up !x.down) <$> it.anyM ((fun x => .up !x.down) <$> p ·) := by
  induction it using IterM.inductSteps with | step it ihy ihs =>
  rw [allM_eq_match_step, anyM_eq_match_step, map_eq_pure_bind, bind_assoc]
  apply bind_congr; intro step
  cases step.inflate using PlausibleIterStep.casesOn
  · simp only [map_eq_pure_bind, bind_assoc, pure_bind]
    apply bind_congr; intro px
    split
    · simp [*, ihy ‹_›]
    · simp [*]
  · simp [ihs ‹_›]
  · simp

theorem IterM.all_eq_not_any_not {α β : Type w} {m : Type w → Type w'} [Iterator α m β]
    [Finite α m] [Monad m] [LawfulMonad m] [IteratorLoop α m m] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} {p : β → Bool} :
    it.all p = (fun x => .up !x.down) <$> it.any (! p ·) := by
  induction it using IterM.inductSteps with | step it ihy ihs =>
  rw [all_eq_match_step, any_eq_match_step, map_eq_pure_bind, bind_assoc]
  apply bind_congr; intro step
  cases step.inflate using PlausibleIterStep.casesOn
  · simp only
    split
    · simp [*, ihy ‹_›]
    · simp [*]
  · simp [ihs ‹_›]
  · simp

theorem IterM.findSomeM?_eq_match_step {α β γ : Type w} {m : Type w → Type w'} [Monad m]
    [Iterator α m β] [IteratorLoop α m m] [LawfulMonad m] [Finite α m] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} {f : β → m (Option γ)} :
    it.findSomeM? f = (do
      match (← it.step).inflate.val with
      | .yield it' out =>
        match ← f out with
        | none => it'.findSomeM? f
        | some fx => return (some fx)
      | .skip it' => it'.findSomeM? f
      | .done => return none) := by
  rw [findSomeM?, forIn_eq_match_step]
  apply bind_congr; intro step
  cases step.inflate using PlausibleIterStep.casesOn
  · simp only [bind_assoc]
    apply bind_congr; intro fx
    split <;> simp [findSomeM?]
  · simp [findSomeM?]
  · simp

theorem IterM.findSome?_eq_findSomeM? {α β γ : Type w} {m : Type w → Type w'} [Monad m]
    [Iterator α m β] [IteratorLoop α m m] [Finite α m]
    {it : IterM (α := α) m β} {f : β → Option γ} :
    it.findSome? f = it.findSomeM? (pure <| f ·) :=
  (rfl)

theorem IterM.findSome?_eq_match_step {α β γ : Type w} {m : Type w → Type w'} [Monad m]
    [Iterator α m β] [IteratorLoop α m m] [LawfulMonad m] [Finite α m] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} {f : β → Option γ} :
    it.findSome? f = (do
      match (← it.step).inflate.val with
      | .yield it' out =>
        match f out with
        | none => it'.findSome? f
        | some fx => return (some fx)
      | .skip it' => it'.findSome? f
      | .done => return none) := by
  rw [findSome?_eq_findSomeM?, findSomeM?_eq_match_step]
  apply bind_congr; intro step
  split <;> simp [findSome?_eq_findSomeM?]

theorem IterM.findSomeM?_pure {α β γ : Type w} {m : Type w → Type w'} [Monad m]
    [Iterator α m β] [IteratorLoop α m m]
    [LawfulMonad m] [Finite α m] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} {f : β → Option γ} :
    it.findSomeM? (pure <| f ·) = it.findSome? f := by
  induction it using IterM.inductSteps with | step it ihy ihs
  rw [findSomeM?_eq_match_step, findSome?_eq_match_step]
  apply bind_congr; intro step
  cases step.inflate using PlausibleIterStep.casesOn
  · simp only [pure_bind]
    split <;> simp [ihy ‹_›]
  · simp [ihs ‹_›]
  · simp

theorem IterM.findM?_eq_findSomeM? {α β : Type w} {m : Type w → Type w'} [Monad m]
    [Iterator α m β] [IteratorLoop α m m] [Finite α m]
    {it : IterM (α := α) m β} {f : β → m (ULift Bool)} :
    it.findM? f = it.findSomeM? (fun x => return if (← f x).down then some x else none) :=
  (rfl)

theorem IterM.findM?_eq_match_step {α β : Type w} {m : Type w → Type w'} [Monad m]
    [Iterator α m β] [IteratorLoop α m m] [LawfulMonad m] [Finite α m] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} {f : β → m (ULift Bool)} :
    it.findM? f = (do
      match (← it.step).inflate.val with
      | .yield it' out =>
        if (← f out).down then return (some out) else it'.findM? f
      | .skip it' => it'.findM? f
      | .done => return none) := by
  rw [findM?_eq_findSomeM?, findSomeM?_eq_match_step]
  apply bind_congr; intro step
  split
  · simp only [bind_assoc]
    apply bind_congr; intro fx
    split <;> simp [findM?_eq_findSomeM?]
  · simp [findM?_eq_findSomeM?]
  · simp

theorem IterM.find?_eq_findM? {α β : Type w} {m : Type w → Type w'} [Monad m] [Iterator α m β]
    [IteratorLoop α m m] [Finite α m] {it : IterM (α := α) m β} {f : β → Bool} :
    it.find? f = it.findM? (pure <| .up <| f ·) :=
  (rfl)

theorem IterM.find?_eq_findSome? {α β : Type w} {m : Type w → Type w'} [Monad m] [Iterator α m β]
    [IteratorLoop α m m] [LawfulMonad m] [Finite α m] {it : IterM (α := α) m β} {f : β → Bool} :
    it.find? f = it.findSome? (fun x => if f x then some x else none) := by
  simp [find?_eq_findM?, findSome?_eq_findSomeM?, findM?_eq_findSomeM?]

theorem IterM.find?_eq_match_step {α β : Type w} {m : Type w → Type w'} [Monad m]
    [Iterator α m β] [IteratorLoop α m m] [LawfulMonad m] [Finite α m] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} {f : β → Bool} :
    it.find? f = (do
      match (← it.step).inflate.val with
      | .yield it' out =>
        if f out then return (some out) else it'.find? f
      | .skip it' => it'.find? f
      | .done => return none) := by
  rw [find?_eq_findM?, findM?_eq_match_step]
  apply bind_congr; intro step
  split
  · simp only [pure_bind]
    split <;> simp [find?_eq_findM?]
  · simp [find?_eq_findM?]
  · simp

theorem IterM.findM?_pure {α β : Type w} {m : Type w → Type w'} [Monad m]
    [Iterator α m β] [IteratorLoop α m m]
    [LawfulMonad m] [Finite α m] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} {f : β → ULift Bool} :
    it.findM? (pure (f := m) <| f ·) = it.find? (ULift.down <| f ·) := by
  induction it using IterM.inductSteps with | step it ihy ihs
  rw [findM?_eq_match_step, find?_eq_match_step]
  apply bind_congr; intro step
  cases step.inflate using PlausibleIterStep.casesOn
  · simp only [pure_bind]
    split
    · simp
    · simp [ihy ‹_›]
  · simp [ihs ‹_›]
  · simp

end Std
