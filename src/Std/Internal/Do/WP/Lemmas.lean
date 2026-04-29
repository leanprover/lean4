/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Gladshtein, Sebastian Graf
-/
module

prelude
public import Std.Internal.Do.WP.Basic
@[expose] public section

set_option linter.missingDocs true

/-!
# Simp lemmas for weakest preconditions

This module provides simp lemmas for simplifying weakest precondition expressions.
Unlike `Std.Do`, we use direct function application `wp x post epost` without notation.

Some lemmas prove only one direction (`⊑`) instead of equality because our `wp_bind` axiom
only provides one direction.
-/

namespace Std.Internal.Do.WPMonad

open Lean.Order WPMonad

universe u v

section
variable {m : Type u → Type v} [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]

/-! ## MonadReaderOf simp lemmas -/

theorem read_ReaderT_wp
    (post : ρ → ρ → Pred) (epost : EPred) :
    (fun r => post r r) ⊑ wp (MonadReaderOf.read : ReaderT ρ m ρ) post epost := by
  intro r
  simpa [MonadReaderOf.read] using
    (WPMonad.wp_pure (m := m) (x := r) (post := fun a => post a r) (epost := epost))

@[simp]
theorem adapt_ReaderT_wp (f : ρ → ρ') (x : ReaderT ρ' m α) :
    wp (ReaderT.adapt f x : ReaderT ρ m α) post epost =
      fun r => wp x (fun a _ => post a r) epost (f r) := rfl

/-! ## MonadStateOf simp lemmas -/

theorem get_StateT_wp
    (post : σ → σ → Pred) (epost : EPred) :
    (fun s => post s s) ⊑ wp (MonadStateOf.get : StateT σ m σ) post epost := by
  intro s
  simpa [MonadStateOf.get] using
    (WPMonad.wp_pure (m := m) (x := (s, s))
      (post := fun x => post x.fst x.snd) (epost := epost))

theorem set_StateT_wp (x : σ)
    (post : PUnit → σ → Pred) (epost : EPred) :
    (fun _ => post ⟨⟩ x) ⊑ wp (MonadStateOf.set x : StateT σ m PUnit) post epost := by
  intro s
  simpa [MonadStateOf.set] using
    (WPMonad.wp_pure (m := m) (x := (PUnit.unit, x))
      (post := fun x => post x.fst x.snd) (epost := epost))

theorem modifyGet_StateT_wp (f : σ → α × σ)
    (post : α → σ → Pred) (epost : EPred) :
    (fun s => post (f s).1 (f s).2) ⊑ wp (MonadStateOf.modifyGet f : StateT σ m α) post epost := by
  intro s
  simpa [MonadStateOf.modifyGet] using
    (WPMonad.wp_pure (m := m) (x := f s)
      (post := fun x => post x.fst x.snd) (epost := epost))

theorem get_EStateM_wp :
    wp (MonadStateOf.get : EStateM ε σ σ) post epost = fun s => post s s := by
  funext s
  simp only [wp, WPMonad.wpTrans, MonadStateOf.get, EStateM.get]

theorem set_EStateM_wp (x : σ) :
    wp (MonadStateOf.set x : EStateM ε σ PUnit) post epost = fun _ => post ⟨⟩ x := by
  funext s
  simp only [wp, WPMonad.wpTrans, MonadStateOf.set, EStateM.set]

theorem modifyGet_EStateM_wp (f : σ → α × σ) :
    wp (MonadStateOf.modifyGet f : EStateM ε σ α) post epost = fun s => post (f s).1 (f s).2 := by
  funext s
  simp only [wp, WPMonad.wpTrans, MonadStateOf.modifyGet, EStateM.modifyGet]

@[simp]
theorem modify_StateT_wp (f : σ → σ) :
    wp (modify f : StateT σ m PUnit) post epost =
      wp (MonadStateOf.modifyGet fun s => (⟨⟩, f s) : StateT σ m PUnit) post epost := by
  rfl

@[simp]
theorem getModify_StateT_wp (f : σ → σ) :
    wp (getModify f : StateT σ m σ) post epost =
      wp (MonadStateOf.modifyGet fun s => (s, f s) : StateT σ m σ) post epost := by
  rfl

theorem modify_EStateM_wp (f : σ → σ) :
    wp (modify f : EStateM ε σ PUnit) post epost =
      wp (MonadStateOf.modifyGet fun s => (⟨⟩, f s) : EStateM ε σ PUnit) post epost := by
  rfl

theorem getModify_EStateM_wp (f : σ → σ) :
    wp (getModify f : EStateM ε σ σ) post epost =
      wp (MonadStateOf.modifyGet fun s => (s, f s) : EStateM ε σ σ) post epost := by
  rfl

/-! ## MonadExceptOf simp lemmas -/

@[simp]
theorem throwThe_wp [MonadExceptOf ε m] (err : ε) :
    wp (throwThe ε err : m α) post epost =
      wp (MonadExceptOf.throw err : m α) post epost := by
  rfl

@[simp]
theorem throw_Except_wp (e : ε) :
    wp (MonadExceptOf.throw e : Except ε α) post epost = epost.head e := by
  simp [wp, WPMonad.wpTrans, MonadExceptOf.throw]

theorem throw_ExceptT_wp (err : ε) :
    epost.head err ⊑ wp (MonadExceptOf.throw err : ExceptT ε m α) post epost := by
  simpa [MonadExceptOf.throw, EPost.cons.pushExcept] using
    (WPMonad.wp_pure (m := m) (x := Except.error err)
      (post := epost.pushExcept post) (epost := epost.tail))

@[simp]
theorem throw_EStateM_wp (e : ε) :
    wp (MonadExceptOf.throw e : EStateM ε σ α) post epost = epost e := by
  funext s
  simp only [wp, WPMonad.wpTrans, MonadExceptOf.throw, EStateM.throw]

@[simp]
theorem throw_Option_wp (e : PUnit) :
    wp (MonadExceptOf.throw e : Option α) post epost = epost := by
  simp only [wp, MonadExceptOf.throw]
  rfl

theorem throw_OptionT_wp (err : PUnit) :
  epost.head ⊑ wp (MonadExceptOf.throw err : OptionT m α) post epost := by
  show epost.head ⊑ wp (pure none : m (Option α)) (epost.pushOption post) epost.tail
  simpa [MonadExceptOf.throw, EPost.cons.pushOption] using
    (WPMonad.wp_pure (m := m) (x := none)
      (post := epost.pushOption post) (epost := epost.tail))

@[simp]
theorem tryCatch_MonadExcept_wp [MonadExceptOf ε m] (x : m α)
    (h : ε → m α) :
    wp (tryCatch x h : m α) post epost =
      wp (MonadExceptOf.tryCatch x h : m α) post epost := by
  rfl

@[simp]
theorem tryCatchThe_wp [MonadExceptOf ε m] (x : m α) (h : ε → m α) :
    wp (tryCatchThe ε x h : m α) post epost =
      wp (MonadExceptOf.tryCatch x h : m α) post epost := by
  rfl

@[simp]
theorem tryCatch_Except_wp (x : Except ε α) (h : ε → Except ε α) :
    wp (MonadExceptOf.tryCatch x h : Except ε α) post epost =
      wp x post epost⟨fun e => wp (h e) post epost⟩ := by
  simp only [wp, WPMonad.wpTrans, MonadExceptOf.tryCatch, Except.tryCatch]
  cases x <;> simp

-- TODO: Upstream
omit [Monad m] in
@[simp] theorem _root_.ExceptT.run_tryCatch [Monad m] [LawfulMonad m]
    (x : ExceptT ε m α) (h : ε → ExceptT ε m α) :
    (tryCatch x h : ExceptT ε m α).run =
      (do
        let r ← x.run
        match r with
        | .ok a => pure (.ok a)
        | .error e => (h e).run) := by
  simp only [tryCatch, tryCatchThe, MonadExceptOf.tryCatch, ExceptT.tryCatch, ExceptT.run_mk]
  rfl

theorem tryCatch_ExceptT_wp (x : ExceptT ε m α)
    (h : ε → ExceptT ε m α) :
    wp x post ⟨fun e => wp (h e) post epost, epost.tail⟩ ⊑
      wp (MonadExceptOf.tryCatch x h : ExceptT ε m α) post epost := by
  change _ ⊑ wp (tryCatch x h : ExceptT ε m α) _ _
  simp only [ExceptT.apply_wp, ExceptT.run_tryCatch]
  apply PartialOrder.rel_trans; rotate_left; apply WPMonad.wp_bind
  apply WPMonad.wp_consequence; intro r; cases r with
  | ok a =>
    simp; apply PartialOrder.rel_trans; rotate_left;
    apply WPMonad.wp_pure; simp; rfl
  | error _ => exact PartialOrder.rel_refl

@[simp]
theorem tryCatch_Option_wp (x : Option α) (h : PUnit → Option α) :
  wp (MonadExceptOf.tryCatch x h : Option α) post epost =
    wp x post (wp (h ⟨⟩) post epost) := by
  simp only [wp, WPMonad.wpTrans, MonadExceptOf.tryCatch, Option.tryCatch]
  cases x <;> rfl


theorem tryCatch_EStateM_wp (x : EStateM ε σ α) (h : ε → EStateM ε σ α) :
    wp (MonadExceptOf.tryCatch x h : EStateM ε σ α) post epost =
      fun s => wp x post (fun e s' => wp (h e) post epost s') s := by
  funext s
  simp only [wp, WPMonad.wpTrans, MonadExceptOf.tryCatch, EStateM.tryCatch]
  cases (x s) <;> simp
  rfl

@[simp]
theorem tryCatch_OptionT_wp (x : OptionT m α)
    (h : PUnit → OptionT m α) :
  wp x post ⟨wp (h ⟨⟩) post epost, epost.tail⟩ ⊑
    wp (MonadExceptOf.tryCatch x h : OptionT m α) post epost := by
  simp only [wp, MonadExceptOf.tryCatch, OptionT.tryCatch, OptionT.mk]
  apply PartialOrder.rel_trans; rotate_left; apply WPMonad.wp_bind
  apply WPMonad.wp_consequence (m := m); intro o; cases o with
  | some a =>
    apply PartialOrder.rel_trans; rotate_left; apply WPMonad.wp_pure
    simp [EPost.cons.pushOption]; exact PartialOrder.rel_refl
  | none => exact PartialOrder.rel_refl

/-! ## Additional state operation lemmas -/

@[simp]
theorem getThe_StateT_wp :
    wp (getThe σ : StateT σ m σ) post epost =
      wp (MonadStateOf.get : StateT σ m σ) post epost := by
  rfl

@[simp]
theorem modifyThe_StateT_wp (f : σ → σ) :
    wp (modifyThe σ f : StateT σ m PUnit) post epost =
      wp (MonadStateOf.modifyGet fun s => (⟨⟩, f s) : StateT σ m PUnit) post epost := by
  rfl

@[simp]
theorem modifyGetThe_StateT_wp (f : σ → α × σ) :
    wp (modifyGetThe σ f : StateT σ m α) post epost =
      wp (MonadStateOf.modifyGet f : StateT σ m α) post epost := by
  rfl

@[simp]
theorem get_MonadState_wp [MonadStateOf σ m] :
    wp (MonadState.get : m σ) post epost =
      wp (MonadStateOf.get : m σ) post epost := by
  rfl

@[simp]
theorem set_MonadState_wp [MonadStateOf σ m] (x : σ) :
    wp (MonadState.set x : m PUnit) post epost =
      wp (MonadStateOf.set x : m PUnit) post epost := by
  rfl

@[simp]
theorem modifyGet_MonadState_wp [MonadStateOf σ m] (f : σ → α × σ) :
    wp (MonadState.modifyGet f : m α) post epost =
      wp (MonadStateOf.modifyGet f : m α) post epost := by
  rfl

@[simp]
theorem read_MonadReader_wp [MonadReaderOf ρ m] :
    wp (MonadReader.read : m ρ) post epost =
      wp (MonadReaderOf.read : m ρ) post epost := by
  rfl

@[simp]
theorem readThe_ReaderT_wp :
    wp (readThe ρ : ReaderT ρ m ρ) post epost =
      wp (MonadReaderOf.read : ReaderT ρ m ρ) post epost := by
  rfl

/-! ## MonadLift simp lemmas -/

theorem monadLift_StateT_wp (x : m α) (post : α → σ → Pred) :
    (fun s => wp x (fun a => post a s) epost) ⊑
      wp (MonadLift.monadLift x : StateT σ m α) post epost := by
  intro s
  simp only [wp, MonadLift.monadLift]
  apply PartialOrder.rel_trans; rotate_left; apply WPMonad.wp_bind
  apply WPMonad.wp_consequence (m := m); intro a
  simpa using
    (WPMonad.wp_pure (m := m) (x := (a, s))
      (post := fun x => post x.fst x.snd) (epost := epost))

@[simp]
theorem monadLift_ReaderT_wp (x : m α) :
    wp (MonadLift.monadLift x : ReaderT ρ m α) post epost =
      fun r => wp x (fun a => post a r) epost := by
  rfl

theorem monadLift_ExceptT_wp (x : m α) (post : α → Pred)
    (epost : EPost.cons (ε → Pred) EPred) :
    wp x post epost.tail ⊑
      wp (MonadLift.monadLift x : ExceptT ε m α) post epost := by
  simp only [wp, MonadLift.monadLift, ExceptT.lift, ExceptT.mk]
  apply PartialOrder.rel_trans; rotate_left
  · exact WPMonad.wp_map (m := m) Except.ok x _ _
  · exact PartialOrder.rel_refl

@[simp]
theorem lift_StateT_wp (x : m α) :
    wp (StateT.lift x : StateT σ m α) post epost =
      wp (MonadLift.monadLift x : StateT σ m α) post epost := by
  rfl

@[simp]
theorem lift_ExceptT_wp (x : m α) :
    wp (ExceptT.lift x : ExceptT ε m α) post epost =
      wp (MonadLift.monadLift x : ExceptT ε m α) post epost := by
  rfl

@[simp]
theorem monadLift_OptionT_wp (x : m α) :
  wp x post epost.tail ⊑
    wp (MonadLift.monadLift x : OptionT m α) post epost := by
  simp only [wp, MonadLift.monadLift, OptionT.mk, OptionT.lift]
  apply PartialOrder.rel_trans; rotate_left; apply WPMonad.wp_bind
  apply WPMonad.wp_consequence (m := m); intro a
  apply PartialOrder.rel_trans; rotate_left; apply WPMonad.wp_pure
  simp [EPost.cons.pushOption]; exact PartialOrder.rel_refl

omit [Assertion EPred] [WPMonad m Pred EPred] in
@[simp]
theorem lift_OptionT_wp
    [Assertion (EPost.cons Pred EPred)] [WPMonad (OptionT m) Pred (EPost.cons Pred EPred)] (x : m α) :
    wp (OptionT.lift x : OptionT m α) post epost =
      wp (MonadLift.monadLift x : OptionT m α) post epost := rfl

/-! ## MonadFunctor simp lemmas -/

@[simp]
theorem monadMap_StateT_wp
    (f : ∀{β}, m β → m β) {α} (x : StateT σ m α) (post : α → σ → Pred) (epost : EPred) :
    wp (MonadFunctor.monadMap (m:=m) f x : StateT σ m α) post epost =
      fun s => wp (f (x.run s)) (fun (a, s') => post a s') epost := by
  funext s
  simp [MonadFunctor.monadMap, StateT.run]

@[simp]
theorem monadMap_ReaderT_wp
    (f : ∀{β}, m β → m β) {α} (x : ReaderT ρ m α) (post : α → ρ → Pred) (epost : EPred) :
    wp (MonadFunctor.monadMap (m:=m) f x : ReaderT ρ m α) post epost =
      fun r => wp (f (x.run r)) (fun a => post a r) epost := by
  funext r
  simp [MonadFunctor.monadMap, ReaderT.run]

@[simp]
theorem monadMap_ExceptT_wp
    (f : ∀{β}, m β → m β) {α} (x : ExceptT ε m α) (post : α → Pred)
    (epost : EPost.cons (ε → Pred) EPred) :
    wp (MonadFunctor.monadMap (m:=m) f x : ExceptT ε m α) post epost =
      wp (f x.run) (epost.pushExcept post) epost.tail := by
  simp [MonadFunctor.monadMap, ExceptT.run]

@[simp]
theorem monadMap_OptionT_wp
  (f : ∀{β}, m β → m β) {α} (x : OptionT m α) (post : α → Pred) (epost : EPost.cons Pred EPred) :
  wp (MonadFunctor.monadMap (m:=m) f x : OptionT m α) post epost =
    wp (f x.run) (epost.pushOption post) epost.tail := by
  simp only [wp, MonadFunctor.monadMap, OptionT.run]; rfl

@[simp]
theorem withReader_ReaderT_wp (f : ρ → ρ) (x : ReaderT ρ m α) :
    wp (MonadWithReaderOf.withReader f x : ReaderT ρ m α) post epost =
      fun r => wp x (fun a _ => post a r) epost (f r) := rfl

@[simp]
theorem withReader_MonadWithReader_wp [MonadWithReaderOf ρ m]
    (f : ρ → ρ) (x : m α) :
    wp (MonadWithReader.withReader f x : m α) post epost =
      wp (MonadWithReaderOf.withReader f x : m α) post epost := rfl

@[simp]
theorem withTheReader_ReaderT_wp (f : ρ → ρ) (x : ReaderT ρ m α) :
    wp (withTheReader ρ f x : ReaderT ρ m α) post epost =
      wp (MonadWithReaderOf.withReader f x : ReaderT ρ m α) post epost := rfl

/-! ## Transformer adapt lemmas -/

theorem adapt_ExceptT_wp (f : ε → ε') (x : ExceptT ε m α) :
    wp x post ⟨fun e => epost.head (f e), epost.tail⟩ ⊑
      wp (ExceptT.adapt f x : ExceptT ε' m α) post epost := by
  simp only [wp, ExceptT.adapt, ExceptT.mk]
  apply PartialOrder.rel_trans; rotate_left
  · exact WPMonad.wp_map (m := m) (Except.mapError f) x _ _
  · apply WPMonad.wp_consequence (m := m); intro r; cases r <;> exact PartialOrder.rel_refl

@[simp]
theorem adaptExcept_EStateM_wp (f : ε → ε') (x : EStateM ε σ α) :
    wp (EStateM.adaptExcept f x : EStateM ε' σ α) post epost =
      wp x post (fun e => epost (f e)) := by
  funext s
  simp only [wp, WPMonad.wpTrans, EStateM.adaptExcept]
  cases (x s) <;> simp

/-! ## MonadControl simp lemmas -/

@[simp]
theorem liftWith_StateT_wp
    (f : (∀{β}, StateT σ m β → m (β × σ)) → m α) :
    wp (MonadControl.liftWith (m:=m) f : StateT σ m α) post epost s =
      wp ((fun a => (a, s)) <$> f (fun x => x.run s)) (fun ⟨a, s⟩ => post a s) epost := by
  simp [MonadControl.liftWith]

@[simp]
theorem liftWith_ReaderT_wp
    (f : (∀{β}, ReaderT ρ m β → m β) → m α) :
    wp (MonadControl.liftWith (m:=m) f : ReaderT ρ m α) post epost r =
      wp (f (fun x => x.run r)) (fun a => post a r) epost := by
  simp [MonadControl.liftWith, ReaderT.run]

-- TODO: Upstream
omit [Monad m] in
@[simp] theorem _root_.ExceptT.run_liftM [Monad m] [LawfulMonad m] (x : m α) :
    (liftM x : ExceptT ε m α).run = (Except.ok <$> x : m (Except ε α)) := rfl

@[simp]
theorem liftWith_ExceptT_wp
    (f : (∀{β}, ExceptT ε m β → m (Except ε β)) → m α) :
    wp (MonadControl.liftWith (m:=m) f : ExceptT ε m α) post epost =
      wp (Except.ok <$> f (fun x => x.run)) (epost.pushExcept post) epost.tail := by
  change wp (liftWith (m:=m) f : ExceptT ε m α) post epost =
    wp (Except.ok <$> f (fun x => x.run)) (epost.pushExcept post) epost.tail
  simp

@[simp]
theorem liftWith_OptionT_wp
  (f : (∀{β}, OptionT m β → m (Option β)) → m α) :
  wp (f (fun x => x.run)) post epost.tail ⊑
    wp (MonadControl.liftWith (m:=m) f : OptionT m α) post epost := by
  simp only [MonadControl.liftWith, liftM, monadLift, OptionT.apply_wp]
  exact monadLift_OptionT_wp (f (fun x => x.run))

theorem restoreM_StateT_wp (x : m (α × σ)) :
    (fun _ => wp x (fun (a, s) => post a s) epost) ⊑
      wp (MonadControl.restoreM (m:=m) x : StateT σ m α) post epost := by
  simp only [MonadControl.restoreM]
  apply PartialOrder.rel_trans; rotate_left; apply WPMonad.wp_bind; simp only [liftM, monadLift]
  apply PartialOrder.rel_trans; rotate_left; apply monadLift_StateT_wp
  intro s; apply WPMonad.wp_consequence; intro s'; simp only
  apply PartialOrder.rel_trans; rotate_left; apply WPMonad.wp_bind
  simp [set, StateT.set, pure, StateT.pure]
  apply PartialOrder.rel_trans
  · simpa using
      (WPMonad.wp_pure (m := m) (x := (s'.fst, s'.snd))
        (post := fun x => post x.fst x.snd) (epost := epost))
  · simpa using
      (WPMonad.wp_pure (m := m) (x := (PUnit.unit, s'.snd))
        (post := fun x => wp (pure (s'.fst, x.snd)) (fun x => post x.fst x.snd) epost)
        (epost := epost))

@[simp]
theorem restoreM_ReaderT_wp (x : m α) :
    wp (MonadControl.restoreM (m:=m) x : ReaderT ρ m α) post epost =
      fun r => wp x (fun a => post a r) epost := by
  funext r
  simp [MonadControl.restoreM, ReaderT.run]

@[simp]
theorem restoreM_ExceptT_wp (x : m (Except ε α)) :
    wp (MonadControl.restoreM (m:=m) x : ExceptT ε m α) post epost =
      wp x (epost.pushExcept post) epost.tail := by
  simp [MonadControl.restoreM, ExceptT.run]

@[simp]
theorem restoreM_OptionT_wp (x : m (Option α)) :
  wp (MonadControl.restoreM (m:=m) x : OptionT m α) post epost =
    wp x (epost.pushOption post) epost.tail := by
  simp only [wp, MonadControl.restoreM]; rfl

end

@[simp]
theorem controlAt_wp [Bind n] [Monad m] [Monad n] [Assertion Pred] [Assertion EPred] [WPMonad n Pred EPred] [MonadControlT m n]
    (f : (∀{β}, n β → m (stM m n β)) → m (stM m n α)) :
    wp (controlAt m f : n α) post epost =
      wp (liftWith f >>= restoreM : n α) post epost := by
  rfl

@[simp]
theorem control_wp [Bind n] [Monad m] [Monad n] [Assertion Pred] [Assertion EPred] [WPMonad n Pred EPred] [MonadControlT m n]
    (f : (∀{β}, n β → m (stM m n β)) → m (stM m n α)) :
    wp (control f : n α) post epost =
      wp (liftWith f >>= restoreM : n α) post epost := by
  rfl

section
variable {m : Type u → Type v} [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]

@[simp]
theorem monadLift_refl_wp [Pure m] (x : m α) :
    wp (MonadLiftT.monadLift x : m α) post epost =
      wp (x : m α) post epost := rfl

@[simp]
theorem monadMap_refl_wp [Pure m] (x : m α) :
    wp (MonadFunctorT.monadMap f x : m α) post epost =
      wp (f x : m α) post epost := by rfl

@[simp]
theorem liftWith_refl_wp [Pure m]
    (f : (∀{β}, m β → m β) → m α) :
    wp (MonadControlT.liftWith (m:=m) f : m α) post epost =
      wp (f (fun x => x) : m α) post epost := by
  rfl

@[simp]
theorem restoreM_refl_wp [Pure m] (x : stM m m α) :
    wp (MonadControlT.restoreM x : m α) post epost =
      wp (Pure.pure x : m α) post epost := by
  rfl

end

/-! ## Transitive lift/map/control simp lemmas -/

section
variable {m n : Type u → Type v} {o : Type u → Type v} [Monad o] [Assertion Pred] [Assertion EPred] [WPMonad o Pred EPred]

@[simp]
theorem monadLift_trans_wp [MonadLift n o] [MonadLiftT m n] (x : m α) :
    wp (MonadLiftT.monadLift x : o α) post epost =
      wp (MonadLift.monadLift (m:=n) (MonadLiftT.monadLift (m:=m) x) : o α) post epost := rfl

@[simp]
theorem monadMap_trans_wp [MonadFunctor n o] [MonadFunctorT m n]
    (x : o α) :
    wp (MonadFunctorT.monadMap f x : o α) post epost =
      wp (MonadFunctor.monadMap (m:=n) (MonadFunctorT.monadMap (m:=m) f) x : o α) post epost := by
  rfl

@[simp]
theorem liftWith_trans_wp [MonadControl n o] [MonadControlT m n]
    (f : (∀{β}, o β → m (stM m o β)) → m α) :
    wp (MonadControlT.liftWith f : o α) post epost =
      wp (MonadControl.liftWith (m:=n) fun x₂ =>
        MonadControlT.liftWith fun x₁ => f (x₁ ∘ x₂) : o α) post epost := by
  rfl

@[simp]
theorem restoreM_trans_wp [MonadControl n o] [MonadControlT m n]
    (x : stM m o α) :
    wp (MonadControlT.restoreM x : o α) post epost =
      wp (MonadControl.restoreM (m:=n) (MonadControlT.restoreM (m:=m) x) : o α)
        post epost := by
  rfl

end

/-! ## Lifted state/reader operations -/

section
variable {m n : Type u → Type v} [Monad n] [MonadLift m n] [Assertion Pred] [Assertion EPred] [WPMonad n Pred EPred]

@[simp]
theorem get_MonadStateOf_lift_wp [MonadStateOf σ m] :
    wp (MonadStateOf.get : n σ) post epost =
      wp (MonadLift.monadLift (MonadStateOf.get : m σ) : n σ) post epost := by
  rfl

@[simp]
theorem set_MonadStateOf_lift_wp [MonadStateOf σ m] (x : σ) :
    wp (MonadStateOf.set x : n PUnit) post epost =
      wp (MonadLift.monadLift (MonadStateOf.set (σ:=σ) x : m PUnit) : n PUnit) post epost := by
  rfl

@[simp]
theorem modifyGet_MonadStateOf_lift_wp [MonadStateOf σ m] (f : σ → α × σ) :
    wp (MonadStateOf.modifyGet f : n α) post epost =
      wp (MonadLift.monadLift (MonadState.modifyGet f : m α) : n α) post epost := by
  rfl

@[simp]
theorem read_MonadReaderOf_lift_wp [MonadReaderOf ρ m] :
    wp (MonadReaderOf.read : n ρ) post epost =
      wp (MonadLift.monadLift (MonadReader.read : m ρ) : n ρ) post epost := by
  rfl

end

/-! ## Lifted except operations -/

section
variable {m : Type u → Type v} [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] [MonadExceptOf ε m]

@[simp]
theorem throw_lift_ExceptT_wp (err : ε) :
    wp (MonadExceptOf.throw (ε:=ε) err : ExceptT ε' m α) post epost =
      wp (MonadExceptOf.throw (ε:=ε) err : m (Except ε' α)) (epost.pushExcept post) epost.tail := by
  rfl

@[simp]
theorem throw_lift_OptionT_wp (err : ε) :
  wp (MonadExceptOf.throw (ε:=ε) err : OptionT m α) post epost =
    wp (MonadExceptOf.throw (ε:=ε) err : m (Option α)) (epost.pushOption post) epost.tail := by
  rfl

@[simp]
theorem tryCatch_lift_ExceptT_wp (x : ExceptT ε' m α) (h : ε → ExceptT ε' m α) :
    wp (MonadExceptOf.tryCatch (ε:=ε) x h : ExceptT ε' m α) post epost =
      wp (MonadExceptOf.tryCatch (ε:=ε) x h : m (Except ε' α))
        (epost.pushExcept post) epost.tail := by
  rfl

@[simp]
theorem tryCatch_lift_OptionT_wp (x : OptionT m α) (h : ε → OptionT m α) :
  wp (MonadExceptOf.tryCatch (ε:=ε) x h : OptionT m α) post epost =
    wp (MonadExceptOf.tryCatch (ε:=ε) x h : m (Option α))
      (epost.pushOption post) epost.tail := by
  rfl

@[simp]
theorem throw_ReaderT_lift_wp (err : ε) :
    wp (MonadExceptOf.throw (ε:=ε) err : ReaderT ρ m α) post epost =
      wp (MonadLift.monadLift (MonadExceptOf.throw (ε:=ε) err : m α) :
        ReaderT ρ m α) post epost := by
  rfl

@[simp]
theorem throw_StateT_lift_wp (err : ε) :
    wp (MonadExceptOf.throw (ε:=ε) err : StateT σ m α) post epost =
      wp (MonadLift.monadLift (MonadExceptOf.throw (ε:=ε) err : m α) :
        StateT σ m α) post epost := by
  rfl

@[simp]
theorem tryCatch_ReaderT_lift_wp (x : ReaderT ρ m α) (h : ε → ReaderT ρ m α) :
    wp (MonadExceptOf.tryCatch (ε:=ε) x h : ReaderT ρ m α) post epost =
      fun r => wp (MonadExceptOf.tryCatch (ε:=ε) (x.run r) (fun e => (h e).run r) : m α)
        (fun a => post a r) epost := by
  rfl

@[simp]
theorem tryCatch_StateT_lift_wp (x : StateT σ m α) (h : ε → StateT σ m α) :
    wp (MonadExceptOf.tryCatch (ε:=ε) x h : StateT σ m α) post epost =
      fun s => wp (MonadExceptOf.tryCatch (ε:=ε) (x.run s) (fun e => (h e).run s) : m (α × σ))
        (fun (a, s') => post a s') epost := by
  rfl

end

/-! ## OrElse simp lemmas -/

@[simp]
theorem orElse_Except_wp (x : Except ε α) (h : Unit → Except ε α) :
    wp (OrElse.orElse x h : Except ε α) post epost =
      wp x post epost⟨fun _ => wp (h ()) post epost⟩ := by
  simp only [wp, OrElse.orElse, MonadExcept.orElse]
  cases x <;> rfl

-- TODO: Upstream
variable {m : Type u → Type v} in
@[simp] theorem _root_.ExceptT.run_orElse [Monad m] [LawfulMonad m]
    (x : ExceptT ε m α) (h : Unit → ExceptT ε m α) :
    (OrElse.orElse x h : ExceptT ε m α).run = (do
      let r ← x.run
      match r with
      | .ok a => pure (.ok a)
      | .error _ => (h ()).run) := by
  simp [OrElse.orElse, MonadExcept.orElse]

section
variable {m : Type u → Type v} [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]

theorem orElse_ExceptT_wp (x : ExceptT ε m α)
    (h : Unit → ExceptT ε m α) :
    wp x post ⟨fun _ => wp (h ()) post epost, epost.tail⟩ ⊑
      wp (OrElse.orElse x h : ExceptT ε m α) post epost := by
  apply tryCatch_ExceptT_wp

@[simp]
theorem orElse_OptionT_wp (x : OptionT m α)
    (h : Unit → OptionT m α) :
  wp x post ⟨wp (h ()) post epost, epost.tail⟩ ⊑
    wp (OrElse.orElse x h : OptionT m α) post epost := by
  simp only [wp, OrElse.orElse]
  apply PartialOrder.rel_trans; rotate_left; apply WPMonad.wp_bind
  apply WPMonad.wp_consequence (m := m); intro o; cases o with
  | some a =>
    apply PartialOrder.rel_trans; rotate_left; apply WPMonad.wp_pure
    simp [EPost.cons.pushOption]; exact PartialOrder.rel_refl
  | none => exact PartialOrder.rel_refl

end

@[simp]
theorem orElse_Option_wp (x : Option α) (h : Unit → Option α) :
  ∀ post (epost : Prop),
  wp (OrElse.orElse x h : Option α) post epost =
    wp x post (wp (h ()) post epost) := by
  simp only [wp, WPMonad.wpTrans, OrElse.orElse, Option.orElse]
  cases x <;> intro _ _ <;> rfl

@[simp]
theorem orElse_EStateM_wp (x : EStateM ε σ α) (h : Unit → EStateM ε σ α) :
    wp (OrElse.orElse x h : EStateM ε σ α) post epost =
      fun s => wp x post (fun _ s' => wp (h ()) post epost s') s := by
  funext s
  simp only [wp, WPMonad.wpTrans, OrElse.orElse, EStateM.orElse]
  cases x s <;> simp; rfl

end Std.Internal.Do.WPMonad
