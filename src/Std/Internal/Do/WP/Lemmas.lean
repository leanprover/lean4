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

Some lemmas prove only one direction (`⊑`) instead of equality because our `bind_le_wp_bind` axiom
only provides one direction.
-/

namespace Std.Internal.Do.WPMonad

open Lean.Order WPMonad

universe u v

section
variable {m : Type u → Type v} [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]

/-! ## MonadReaderOf simp lemmas -/

theorem le_wp_read_ReaderT_apply
    (post : ρ → ρ → Pred) (epost : EPred) :
    (fun r => post r r) ⊑ wp (MonadReaderOf.read : ReaderT ρ m ρ) post epost := by
  intro r
  simpa [MonadReaderOf.read] using
    (WPMonad.pure_le_wp_pure (m := m) (x := r) (post := fun a => post a r) (epost := epost))

@[simp]
theorem wp_adapt_ReaderT_apply_eq (f : ρ → ρ') (x : ReaderT ρ' m α) :
    wp (ReaderT.adapt f x : ReaderT ρ m α) post epost =
      fun r => wp x (fun a _ => post a r) epost (f r) := rfl

/-! ## MonadStateOf simp lemmas -/

theorem le_wp_get_StateT_apply
    (post : σ → σ → Pred) (epost : EPred) :
    (fun s => post s s) ⊑ wp (MonadStateOf.get : StateT σ m σ) post epost := by
  intro s
  simpa [MonadStateOf.get] using!
    (WPMonad.pure_le_wp_pure (m := m) (x := (s, s))
      (post := fun x => post x.fst x.snd) (epost := epost))

theorem le_wp_set_StateT_apply (x : σ)
    (post : PUnit → σ → Pred) (epost : EPred) :
    (fun _ => post ⟨⟩ x) ⊑ wp (MonadStateOf.set x : StateT σ m PUnit) post epost := by
  intro s
  simpa [MonadStateOf.set] using!
    (WPMonad.pure_le_wp_pure (m := m) (x := (PUnit.unit, x))
      (post := fun x => post x.fst x.snd) (epost := epost))

theorem le_wp_modifyGet_StateT_apply (f : σ → α × σ)
    (post : α → σ → Pred) (epost : EPred) :
    (fun s => post (f s).1 (f s).2) ⊑ wp (MonadStateOf.modifyGet f : StateT σ m α) post epost := by
  intro s
  simpa [MonadStateOf.modifyGet] using!
    (WPMonad.pure_le_wp_pure (m := m) (x := f s)
      (post := fun x => post x.fst x.snd) (epost := epost))

theorem wp_get_EStateM_apply_eq :
    wp (MonadStateOf.get : EStateM ε σ σ) post epost = fun s => post s s := by
  funext s
  simp only [wp, WP.wpTrans, MonadStateOf.get, EStateM.get]

theorem wp_set_EStateM_apply_eq (x : σ) :
    wp (MonadStateOf.set x : EStateM ε σ PUnit) post epost = fun _ => post ⟨⟩ x := by
  funext s
  simp only [wp, WP.wpTrans, MonadStateOf.set, EStateM.set]

theorem wp_modifyGet_EStateM_apply_eq (f : σ → α × σ) :
    wp (MonadStateOf.modifyGet f : EStateM ε σ α) post epost = fun s => post (f s).1 (f s).2 := by
  funext s
  simp only [wp, WP.wpTrans, MonadStateOf.modifyGet, EStateM.modifyGet]

@[simp]
theorem wp_modify_StateT_apply_eq (f : σ → σ) :
    wp (modify f : StateT σ m PUnit) post epost =
      wp (MonadStateOf.modifyGet fun s => (⟨⟩, f s) : StateT σ m PUnit) post epost := by
  rfl

@[simp]
theorem wp_getModify_StateT_apply_eq (f : σ → σ) :
    wp (getModify f : StateT σ m σ) post epost =
      wp (MonadStateOf.modifyGet fun s => (s, f s) : StateT σ m σ) post epost := by
  rfl

theorem wp_modify_EStateM_apply_eq (f : σ → σ) :
    wp (modify f : EStateM ε σ PUnit) post epost =
      wp (MonadStateOf.modifyGet fun s => (⟨⟩, f s) : EStateM ε σ PUnit) post epost := by
  rfl

theorem wp_getModify_EStateM_apply_eq (f : σ → σ) :
    wp (getModify f : EStateM ε σ σ) post epost =
      wp (MonadStateOf.modifyGet fun s => (s, f s) : EStateM ε σ σ) post epost := by
  rfl

/-! ## MonadExceptOf simp lemmas -/

@[simp]
theorem wp_throwThe_apply_eq [MonadExceptOf ε m] (err : ε) :
    wp (throwThe ε err : m α) post epost =
      wp (MonadExceptOf.throw err : m α) post epost := by
  rfl

@[simp]
theorem wp_throw_Except_apply_eq (e : ε) :
    wp (MonadExceptOf.throw e : Except ε α) post epost = epost.head e := by
  simp [wp, WP.wpTrans, MonadExceptOf.throw]

theorem le_wp_throw_ExceptT_apply (err : ε) :
    epost.head err ⊑ wp (MonadExceptOf.throw err : ExceptT ε m α) post epost := by
  simpa [MonadExceptOf.throw, EPost.Cons.pushExcept] using
    (WPMonad.pure_le_wp_pure (m := m) (x := Except.error err)
      (post := epost.pushExcept post) (epost := epost.tail))

@[simp]
theorem wp_throw_EStateM_apply_eq (e : ε) :
    wp (MonadExceptOf.throw e : EStateM ε σ α) post epost = epost e := by
  funext s
  simp only [wp, WP.wpTrans, MonadExceptOf.throw, EStateM.throw]

@[simp]
theorem wp_throw_Option_apply_eq (e : PUnit) :
    wp (MonadExceptOf.throw e : Option α) post epost = epost := by
  simp only [wp, MonadExceptOf.throw]
  rfl

theorem le_wp_throw_OptionT_apply (err : PUnit) :
  epost.head ⊑ wp (MonadExceptOf.throw err : OptionT m α) post epost := by
  show epost.head ⊑ wp (pure none : m (Option α)) (epost.pushOption post) epost.tail
  simpa [MonadExceptOf.throw, EPost.Cons.pushOption] using
    (WPMonad.pure_le_wp_pure (m := m) (x := none)
      (post := epost.pushOption post) (epost := epost.tail))

@[simp]
theorem wp_tryCatch_MonadExcept_apply_eq [MonadExceptOf ε m] (x : m α)
    (h : ε → m α) :
    wp (tryCatch x h : m α) post epost =
      wp (MonadExceptOf.tryCatch x h : m α) post epost := by
  rfl

@[simp]
theorem wp_tryCatchThe_apply_eq [MonadExceptOf ε m] (x : m α) (h : ε → m α) :
    wp (tryCatchThe ε x h : m α) post epost =
      wp (MonadExceptOf.tryCatch x h : m α) post epost := by
  rfl

@[simp]
theorem wp_tryCatch_Except_apply_eq (x : Except ε α) (h : ε → Except ε α) :
    wp (MonadExceptOf.tryCatch x h : Except ε α) post epost =
      wp x post epost⟨fun e => wp (h e) post epost⟩ := by
  simp only [wp, WP.wpTrans, MonadExceptOf.tryCatch, Except.tryCatch]
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

theorem le_wp_tryCatch_ExceptT_apply (x : ExceptT ε m α)
    (h : ε → ExceptT ε m α) :
    wp x post ⟨fun e => wp (h e) post epost, epost.tail⟩ ⊑
      wp (MonadExceptOf.tryCatch x h : ExceptT ε m α) post epost := by
  change _ ⊑ wp (tryCatch x h : ExceptT ε m α) _ _
  simp only [ExceptT.wp_apply_eq, ExceptT.run_tryCatch]
  apply PartialOrder.rel_trans; rotate_left; apply WPMonad.bind_le_wp_bind
  apply WP.wp_consequence; intro r; cases r with
  | ok a =>
    simp; apply PartialOrder.rel_trans; rotate_left;
    apply WPMonad.pure_le_wp_pure; simp; rfl
  | error _ => exact PartialOrder.rel_refl

@[simp]
theorem wp_tryCatch_Option_apply_eq (x : Option α) (h : PUnit → Option α) :
  wp (MonadExceptOf.tryCatch x h : Option α) post epost =
    wp x post (wp (h ⟨⟩) post epost) := by
  simp only [wp, WP.wpTrans, MonadExceptOf.tryCatch, Option.tryCatch]
  cases x <;> rfl


theorem wp_tryCatch_EStateM_apply_eq (x : EStateM ε σ α) (h : ε → EStateM ε σ α) :
    wp (MonadExceptOf.tryCatch x h : EStateM ε σ α) post epost =
      fun s => wp x post (fun e s' => wp (h e) post epost s') s := by
  funext s
  simp only [wp, WP.wpTrans, MonadExceptOf.tryCatch, EStateM.tryCatch]
  cases (x s) <;> simp
  rfl

@[simp]
theorem le_wp_tryCatch_OptionT_apply (x : OptionT m α)
    (h : PUnit → OptionT m α) :
  wp x post ⟨wp (h ⟨⟩) post epost, epost.tail⟩ ⊑
    wp (MonadExceptOf.tryCatch x h : OptionT m α) post epost := by
  simp only [wp, MonadExceptOf.tryCatch, OptionT.tryCatch, OptionT.mk]
  apply PartialOrder.rel_trans; rotate_left; apply WPMonad.bind_le_wp_bind
  apply WP.wp_consequence (x := x.run); intro o; cases o with
  | some a =>
    apply PartialOrder.rel_trans; rotate_left; apply WPMonad.pure_le_wp_pure
    simp [EPost.Cons.pushOption]; exact PartialOrder.rel_refl
  | none => exact PartialOrder.rel_refl

/-! ## Additional state operation lemmas -/

@[simp]
theorem wp_getThe_StateT_apply_eq :
    wp (getThe σ : StateT σ m σ) post epost =
      wp (MonadStateOf.get : StateT σ m σ) post epost := by
  rfl

@[simp]
theorem wp_modifyThe_StateT_apply_eq (f : σ → σ) :
    wp (modifyThe σ f : StateT σ m PUnit) post epost =
      wp (MonadStateOf.modifyGet fun s => (⟨⟩, f s) : StateT σ m PUnit) post epost := by
  rfl

@[simp]
theorem wp_modifyGetThe_StateT_apply_eq (f : σ → α × σ) :
    wp (modifyGetThe σ f : StateT σ m α) post epost =
      wp (MonadStateOf.modifyGet f : StateT σ m α) post epost := by
  rfl

@[simp]
theorem wp_get_MonadState_apply_eq [MonadStateOf σ m] :
    wp (MonadState.get : m σ) post epost =
      wp (MonadStateOf.get : m σ) post epost := by
  rfl

@[simp]
theorem wp_set_MonadState_apply_eq [MonadStateOf σ m] (x : σ) :
    wp (MonadState.set x : m PUnit) post epost =
      wp (MonadStateOf.set x : m PUnit) post epost := by
  rfl

@[simp]
theorem wp_modifyGet_MonadState_apply_eq [MonadStateOf σ m] (f : σ → α × σ) :
    wp (MonadState.modifyGet f : m α) post epost =
      wp (MonadStateOf.modifyGet f : m α) post epost := by
  rfl

@[simp]
theorem wp_read_MonadReader_apply_eq [MonadReaderOf ρ m] :
    wp (MonadReader.read : m ρ) post epost =
      wp (MonadReaderOf.read : m ρ) post epost := by
  rfl

@[simp]
theorem wp_readThe_ReaderT_apply_eq :
    wp (readThe ρ : ReaderT ρ m ρ) post epost =
      wp (MonadReaderOf.read : ReaderT ρ m ρ) post epost := by
  rfl

/-! ## MonadLift simp lemmas -/

theorem le_wp_monadLift_StateT_apply (x : m α) (post : α → σ → Pred) :
    (fun s => wp x (fun a => post a s) epost) ⊑
      wp (MonadLift.monadLift x : StateT σ m α) post epost := by
  intro s
  simp only [wp, MonadLift.monadLift]
  apply PartialOrder.rel_trans; rotate_left; apply WPMonad.bind_le_wp_bind
  apply WP.wp_consequence; intro a
  simpa using
    (WPMonad.pure_le_wp_pure (m := m) (x := (a, s))
      (post := fun x => post x.fst x.snd) (epost := epost))

@[simp]
theorem wp_monadLift_ReaderT_apply_eq (x : m α) :
    wp (MonadLift.monadLift x : ReaderT ρ m α) post epost =
      fun r => wp x (fun a => post a r) epost := by
  rfl

theorem le_wp_monadLift_ExceptT_apply (x : m α) (post : α → Pred)
    (epost : EPost.Cons (ε → Pred) EPred) :
    wp x post epost.tail ⊑
      wp (MonadLift.monadLift x : ExceptT ε m α) post epost := by
  simp only [wp, MonadLift.monadLift, ExceptT.lift, ExceptT.mk]
  apply PartialOrder.rel_trans; rotate_left
  · exact WPMonad.map_le_wp_map (m := m) Except.ok x _ _
  · exact PartialOrder.rel_refl

@[simp]
theorem wp_lift_StateT_apply_eq (x : m α) :
    wp (StateT.lift x : StateT σ m α) post epost =
      wp (MonadLift.monadLift x : StateT σ m α) post epost := by
  rfl

@[simp]
theorem wp_lift_ExceptT_apply_eq (x : m α) :
    wp (ExceptT.lift x : ExceptT ε m α) post epost =
      wp (MonadLift.monadLift x : ExceptT ε m α) post epost := by
  rfl

@[simp]
theorem le_wp_monadLift_OptionT_apply (x : m α) :
  wp x post epost.tail ⊑
    wp (MonadLift.monadLift x : OptionT m α) post epost := by
  simp only [wp, MonadLift.monadLift, OptionT.mk, OptionT.lift]
  apply PartialOrder.rel_trans; rotate_left; apply WPMonad.bind_le_wp_bind
  apply WP.wp_consequence; intro a
  apply PartialOrder.rel_trans; rotate_left; apply WPMonad.pure_le_wp_pure
  simp [EPost.Cons.pushOption]; exact PartialOrder.rel_refl

@[simp]
theorem wp_lift_OptionT_apply_eq (x : m α) :
    wp (OptionT.lift x : OptionT m α) post epost =
      wp (MonadLift.monadLift x : OptionT m α) post epost := rfl

/-! ## MonadFunctor simp lemmas -/

@[simp]
theorem wp_monadMap_StateT_apply_eq
    (f : ∀{β}, m β → m β) {α} (x : StateT σ m α) (post : α → σ → Pred) (epost : EPred) :
    wp (MonadFunctor.monadMap (m:=m) f x : StateT σ m α) post epost =
      fun s => wp (f (x.run s)) (fun (a, s') => post a s') epost := by
  funext s
  simp [MonadFunctor.monadMap, StateT.run]

@[simp]
theorem wp_monadMap_ReaderT_apply_eq
    (f : ∀{β}, m β → m β) {α} (x : ReaderT ρ m α) (post : α → ρ → Pred) (epost : EPred) :
    wp (MonadFunctor.monadMap (m:=m) f x : ReaderT ρ m α) post epost =
      fun r => wp (f (x.run r)) (fun a => post a r) epost := by
  funext r
  simp [MonadFunctor.monadMap, ReaderT.run]

@[simp]
theorem wp_monadMap_ExceptT_apply_eq
    (f : ∀{β}, m β → m β) {α} (x : ExceptT ε m α) (post : α → Pred)
    (epost : EPost.Cons (ε → Pred) EPred) :
    wp (MonadFunctor.monadMap (m:=m) f x : ExceptT ε m α) post epost =
      wp (f x.run) (epost.pushExcept post) epost.tail := by
  simp [MonadFunctor.monadMap, ExceptT.run]

@[simp]
theorem wp_monadMap_OptionT_apply_eq
  (f : ∀{β}, m β → m β) {α} (x : OptionT m α) (post : α → Pred) (epost : EPost.Cons Pred EPred) :
  wp (MonadFunctor.monadMap (m:=m) f x : OptionT m α) post epost =
    wp (f x.run) (epost.pushOption post) epost.tail := by
  simp only [wp, MonadFunctor.monadMap, OptionT.run]; rfl

@[simp]
theorem wp_withReader_ReaderT_apply_eq (f : ρ → ρ) (x : ReaderT ρ m α) :
    wp (MonadWithReaderOf.withReader f x : ReaderT ρ m α) post epost =
      fun r => wp x (fun a _ => post a r) epost (f r) := rfl

@[simp]
theorem wp_withReader_MonadWithReader_apply_eq [MonadWithReaderOf ρ m]
    (f : ρ → ρ) (x : m α) :
    wp (MonadWithReader.withReader f x : m α) post epost =
      wp (MonadWithReaderOf.withReader f x : m α) post epost := rfl

@[simp]
theorem wp_withTheReader_ReaderT_apply_eq (f : ρ → ρ) (x : ReaderT ρ m α) :
    wp (withTheReader ρ f x : ReaderT ρ m α) post epost =
      wp (MonadWithReaderOf.withReader f x : ReaderT ρ m α) post epost := rfl

/-! ## Transformer adapt lemmas -/

theorem le_wp_adapt_ExceptT_apply (f : ε → ε') (x : ExceptT ε m α) :
    wp x post ⟨fun e => epost.head (f e), epost.tail⟩ ⊑
      wp (ExceptT.adapt f x : ExceptT ε' m α) post epost := by
  simp only [wp, ExceptT.adapt, ExceptT.mk]
  apply PartialOrder.rel_trans; rotate_left
  · exact WPMonad.map_le_wp_map (m := m) (Except.mapError f) x _ _
  · apply WP.wp_consequence (x := x.run); intro r; cases r <;> exact PartialOrder.rel_refl

@[simp]
theorem wp_adaptExcept_EStateM_apply_eq (f : ε → ε') (x : EStateM ε σ α) :
    wp (EStateM.adaptExcept f x : EStateM ε' σ α) post epost =
      wp x post (fun e => epost (f e)) := by
  funext s
  simp only [wp, WP.wpTrans, EStateM.adaptExcept]
  cases (x s) <;> simp

/-! ## MonadControl simp lemmas -/

@[simp]
theorem wp_liftWith_StateT_apply_eq
    (f : (∀{β}, StateT σ m β → m (β × σ)) → m α) :
    wp (MonadControl.liftWith (m:=m) f : StateT σ m α) post epost s =
      wp ((fun a => (a, s)) <$> f (fun x => x.run s)) (fun ⟨a, s⟩ => post a s) epost := by
  simp [MonadControl.liftWith]

@[simp]
theorem wp_liftWith_ReaderT_apply_eq
    (f : (∀{β}, ReaderT ρ m β → m β) → m α) :
    wp (MonadControl.liftWith (m:=m) f : ReaderT ρ m α) post epost r =
      wp (f (fun x => x.run r)) (fun a => post a r) epost := by
  simp [MonadControl.liftWith, ReaderT.run]

-- TODO: Upstream
omit [Monad m] in
@[simp] theorem _root_.ExceptT.run_liftM [Monad m] [LawfulMonad m] (x : m α) :
    (liftM x : ExceptT ε m α).run = (Except.ok <$> x : m (Except ε α)) := rfl

@[simp]
theorem wp_liftWith_ExceptT_apply_eq
    (f : (∀{β}, ExceptT ε m β → m (Except ε β)) → m α) :
    wp (MonadControl.liftWith (m:=m) f : ExceptT ε m α) post epost =
      wp (Except.ok <$> f (fun x => x.run)) (epost.pushExcept post) epost.tail := by
  change wp (liftWith (m:=m) f : ExceptT ε m α) post epost =
    wp (Except.ok <$> f (fun x => x.run)) (epost.pushExcept post) epost.tail
  simp

@[simp]
theorem le_wp_liftWith_OptionT_apply
  (f : (∀{β}, OptionT m β → m (Option β)) → m α) :
  wp (f (fun x => x.run)) post epost.tail ⊑
    wp (MonadControl.liftWith (m:=m) f : OptionT m α) post epost := by
  simp only [MonadControl.liftWith, liftM, monadLift, OptionT.wp_apply_eq]
  exact le_wp_monadLift_OptionT_apply (f (fun x => x.run))

theorem le_wp_restoreM_StateT_apply (x : m (α × σ)) :
    (fun _ => wp x (fun (a, s) => post a s) epost) ⊑
      wp (MonadControl.restoreM (m:=m) x : StateT σ m α) post epost := by
  simp only [MonadControl.restoreM]
  apply PartialOrder.rel_trans; rotate_left; apply WPMonad.bind_le_wp_bind; simp only [liftM, monadLift]
  apply PartialOrder.rel_trans; rotate_left; apply le_wp_monadLift_StateT_apply
  intro s; apply WP.wp_consequence (x := x); intro s'; simp only
  apply PartialOrder.rel_trans; rotate_left; apply WPMonad.bind_le_wp_bind
  simp [set, StateT.set, pure, StateT.pure]
  apply PartialOrder.rel_trans
  · simpa using
      (WPMonad.pure_le_wp_pure (m := m) (x := (s'.fst, s'.snd))
        (post := fun x => post x.fst x.snd) (epost := epost))
  · simpa using
      (WPMonad.pure_le_wp_pure (m := m) (x := (PUnit.unit, s'.snd))
        (post := fun (x : PUnit × σ) => wp (pure (s'.fst, x.snd)) (fun (x : α × σ) => post x.fst x.snd) epost)
        (epost := epost))

@[simp]
theorem wp_restoreM_ReaderT_apply_eq (x : m α) :
    wp (MonadControl.restoreM (m:=m) x : ReaderT ρ m α) post epost =
      fun r => wp x (fun a => post a r) epost := by
  funext r
  simp [MonadControl.restoreM, ReaderT.run]

@[simp]
theorem wp_restoreM_ExceptT_apply_eq (x : m (Except ε α)) :
    wp (MonadControl.restoreM (m:=m) x : ExceptT ε m α) post epost =
      wp x (epost.pushExcept post) epost.tail := by
  simp [MonadControl.restoreM, ExceptT.run]

@[simp]
theorem wp_restoreM_OptionT_apply_eq (x : m (Option α)) :
  wp (MonadControl.restoreM (m:=m) x : OptionT m α) post epost =
    wp x (epost.pushOption post) epost.tail := by
  simp only [wp, MonadControl.restoreM]; rfl

end

@[simp]
theorem wp_controlAt_apply_eq [Bind n] [Monad m] [Monad n] [Assertion Pred] [Assertion EPred] [∀ α, WP (n α) α Pred EPred] [MonadControlT m n]
    (f : (∀{β}, n β → m (stM m n β)) → m (stM m n α)) :
    wp (controlAt m f : n α) post epost =
      wp (liftWith f >>= restoreM : n α) post epost := by
  rfl

@[simp]
theorem wp_control_apply_eq [Bind n] [Monad m] [Monad n] [Assertion Pred] [Assertion EPred] [∀ α, WP (n α) α Pred EPred] [MonadControlT m n]
    (f : (∀{β}, n β → m (stM m n β)) → m (stM m n α)) :
    wp (control f : n α) post epost =
      wp (liftWith f >>= restoreM : n α) post epost := by
  rfl

section
variable {m : Type u → Type v} [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]

@[simp]
theorem wp_monadLift_refl_apply_eq [Pure m] (x : m α) :
    wp (MonadLiftT.monadLift x : m α) post epost =
      wp (x : m α) post epost := rfl

@[simp]
theorem wp_monadMap_refl_apply_eq [Pure m] (x : m α) :
    wp (MonadFunctorT.monadMap f x : m α) post epost =
      wp (f x : m α) post epost := by rfl

@[simp]
theorem wp_liftWith_refl_apply_eq [Pure m]
    (f : (∀{β}, m β → m β) → m α) :
    wp (MonadControlT.liftWith (m:=m) f : m α) post epost =
      wp (f (fun x => x) : m α) post epost := by
  rfl

@[simp]
theorem wp_restoreM_refl_apply_eq [Pure m] (x : stM m m α) :
    wp (MonadControlT.restoreM x : m α) post epost =
      wp (Pure.pure x : m α) post epost := by
  rfl

end

/-! ## Transitive lift/map/control simp lemmas -/

section
variable {m n : Type u → Type v} {o : Type u → Type v} [Assertion Pred] [Assertion EPred] [∀ α, WP (o α) α Pred EPred]

@[simp]
theorem wp_monadLift_trans_apply_eq [MonadLift n o] [MonadLiftT m n] (x : m α) :
    wp (MonadLiftT.monadLift x : o α) post epost =
      wp (MonadLift.monadLift (m:=n) (MonadLiftT.monadLift (m:=m) x) : o α) post epost := rfl

@[simp]
theorem wp_monadMap_trans_apply_eq [MonadFunctor n o] [MonadFunctorT m n]
    (x : o α) :
    wp (MonadFunctorT.monadMap f x : o α) post epost =
      wp (MonadFunctor.monadMap (m:=n) (MonadFunctorT.monadMap (m:=m) f) x : o α) post epost := by
  rfl

@[simp]
theorem wp_liftWith_trans_apply_eq [MonadControl n o] [MonadControlT m n]
    (f : (∀{β}, o β → m (stM m o β)) → m α) :
    wp (MonadControlT.liftWith f : o α) post epost =
      wp (MonadControl.liftWith (m:=n) fun x₂ =>
        MonadControlT.liftWith fun x₁ => f (x₁ ∘ x₂) : o α) post epost := by
  rfl

@[simp]
theorem wp_restoreM_trans_apply_eq [MonadControl n o] [MonadControlT m n]
    (x : stM m o α) :
    wp (MonadControlT.restoreM x : o α) post epost =
      wp (MonadControl.restoreM (m:=n) (MonadControlT.restoreM (m:=m) x) : o α)
        post epost := by
  rfl

end

/-! ## Lifted state/reader operations -/

section
variable {m n : Type u → Type v} [MonadLift m n] [Assertion Pred] [Assertion EPred] [∀ α, WP (n α) α Pred EPred]

@[simp]
theorem wp_get_MonadStateOf_lift_apply_eq [MonadStateOf σ m] :
    wp (MonadStateOf.get : n σ) post epost =
      wp (MonadLift.monadLift (MonadStateOf.get : m σ) : n σ) post epost := by
  rfl

@[simp]
theorem wp_set_MonadStateOf_lift_apply_eq [MonadStateOf σ m] (x : σ) :
    wp (MonadStateOf.set x : n PUnit) post epost =
      wp (MonadLift.monadLift (MonadStateOf.set (σ:=σ) x : m PUnit) : n PUnit) post epost := by
  rfl

@[simp]
theorem wp_modifyGet_MonadStateOf_lift_apply_eq [MonadStateOf σ m] (f : σ → α × σ) :
    wp (MonadStateOf.modifyGet f : n α) post epost =
      wp (MonadLift.monadLift (MonadState.modifyGet f : m α) : n α) post epost := by
  rfl

@[simp]
theorem wp_read_MonadReaderOf_lift_apply_eq [MonadReaderOf ρ m] :
    wp (MonadReaderOf.read : n ρ) post epost =
      wp (MonadLift.monadLift (MonadReader.read : m ρ) : n ρ) post epost := by
  rfl

end

/-! ## Lifted except operations -/

section
variable {m : Type u → Type v} [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] [MonadExceptOf ε m]

@[simp]
theorem wp_throw_lift_ExceptT_apply_eq (err : ε) :
    wp (MonadExceptOf.throw (ε:=ε) err : ExceptT ε' m α) post epost =
      wp (MonadExceptOf.throw (ε:=ε) err : m (Except ε' α)) (epost.pushExcept post) epost.tail := by
  rfl

@[simp]
theorem wp_throw_lift_OptionT_apply_eq (err : ε) :
  wp (MonadExceptOf.throw (ε:=ε) err : OptionT m α) post epost =
    wp (MonadExceptOf.throw (ε:=ε) err : m (Option α)) (epost.pushOption post) epost.tail := by
  rfl

@[simp]
theorem wp_tryCatch_lift_ExceptT_apply_eq (x : ExceptT ε' m α) (h : ε → ExceptT ε' m α) :
    wp (MonadExceptOf.tryCatch (ε:=ε) x h : ExceptT ε' m α) post epost =
      wp (MonadExceptOf.tryCatch (ε:=ε) x h : m (Except ε' α))
        (epost.pushExcept post) epost.tail := by
  rfl

@[simp]
theorem wp_tryCatch_lift_OptionT_apply_eq (x : OptionT m α) (h : ε → OptionT m α) :
  wp (MonadExceptOf.tryCatch (ε:=ε) x h : OptionT m α) post epost =
    wp (MonadExceptOf.tryCatch (ε:=ε) x h : m (Option α))
      (epost.pushOption post) epost.tail := by
  rfl

@[simp]
theorem wp_throw_ReaderT_lift_apply_eq (err : ε) :
    wp (MonadExceptOf.throw (ε:=ε) err : ReaderT ρ m α) post epost =
      wp (MonadLift.monadLift (MonadExceptOf.throw (ε:=ε) err : m α) :
        ReaderT ρ m α) post epost := by
  rfl

@[simp]
theorem wp_throw_StateT_lift_apply_eq (err : ε) :
    wp (MonadExceptOf.throw (ε:=ε) err : StateT σ m α) post epost =
      wp (MonadLift.monadLift (MonadExceptOf.throw (ε:=ε) err : m α) :
        StateT σ m α) post epost := by
  rfl

@[simp]
theorem wp_tryCatch_ReaderT_lift_apply_eq (x : ReaderT ρ m α) (h : ε → ReaderT ρ m α) :
    wp (MonadExceptOf.tryCatch (ε:=ε) x h : ReaderT ρ m α) post epost =
      fun r => wp (MonadExceptOf.tryCatch (ε:=ε) (x.run r) (fun e => (h e).run r) : m α)
        (fun a => post a r) epost := by
  rfl

@[simp]
theorem wp_tryCatch_StateT_lift_apply_eq (x : StateT σ m α) (h : ε → StateT σ m α) :
    wp (MonadExceptOf.tryCatch (ε:=ε) x h : StateT σ m α) post epost =
      fun s => wp (MonadExceptOf.tryCatch (ε:=ε) (x.run s) (fun e => (h e).run s) : m (α × σ))
        (fun (a, s') => post a s') epost := by
  rfl

end

/-! ## OrElse simp lemmas -/

@[simp]
theorem wp_orElse_Except_apply_eq (x : Except ε α) (h : Unit → Except ε α) :
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

theorem le_wp_orElse_ExceptT_apply (x : ExceptT ε m α)
    (h : Unit → ExceptT ε m α) :
    wp x post ⟨fun _ => wp (h ()) post epost, epost.tail⟩ ⊑
      wp (OrElse.orElse x h : ExceptT ε m α) post epost := by
  apply le_wp_tryCatch_ExceptT_apply

@[simp]
theorem le_wp_orElse_OptionT_apply (x : OptionT m α)
    (h : Unit → OptionT m α) :
  wp x post ⟨wp (h ()) post epost, epost.tail⟩ ⊑
    wp (OrElse.orElse x h : OptionT m α) post epost := by
  simp only [wp, OrElse.orElse]
  apply PartialOrder.rel_trans; rotate_left; apply WPMonad.bind_le_wp_bind
  apply WP.wp_consequence (x := x.run); intro o; cases o with
  | some a =>
    apply PartialOrder.rel_trans; rotate_left; apply WPMonad.pure_le_wp_pure
    simp [EPost.Cons.pushOption]; exact PartialOrder.rel_refl
  | none => exact PartialOrder.rel_refl

end

@[simp]
theorem wp_orElse_Option_apply_eq (x : Option α) (h : Unit → Option α) :
  ∀ post (epost : Prop),
  wp (OrElse.orElse x h : Option α) post epost =
    wp x post (wp (h ()) post epost) := by
  simp only [wp, WP.wpTrans, OrElse.orElse, Option.orElse]
  cases x <;> intro _ _ <;> rfl

@[simp]
theorem wp_orElse_EStateM_apply_eq (x : EStateM ε σ α) (h : Unit → EStateM ε σ α) :
    wp (OrElse.orElse x h : EStateM ε σ α) post epost =
      fun s => wp x post (fun _ s' => wp (h ()) post epost s') s := by
  funext s
  simp only [wp, WP.wpTrans, OrElse.orElse, EStateM.orElse]
  cases x s <;> simp; rfl

end Std.Internal.Do.WPMonad
