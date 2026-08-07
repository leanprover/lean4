/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Gladshtein, Sebastian Graf
-/
module

prelude
public import Std.Internal.Do.Triple.Basic
public import Std.Do.Triple.SpecLemmas
public import Init.Data.Range.Polymorphic.Iterators
import Init.Data.Range.Polymorphic
public import Init.Data.Slice.Array

-- This public import is a workaround for #10652.
-- Without it, adding the `spec` attribute for `instMonadLiftTOfMonadLift` will fail.
public import Init.Data.Iterators.Lemmas.Combinators.FilterMap
public import Init.Data.Range
import Init.Data.Iterators.Lemmas
import Init.Data.List.Nat.Range
import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Range
import Init.Data.List.TakeDrop
import Init.Data.Nat.Mod
import Init.Data.Slice.Lemmas
import Init.Omega
public import Init.Data.String.Defs
public import Init.Data.String.Iterate
import Init.Data.String.Lemmas.Splits
import Init.Data.String.Termination
import Init.Data.String.Lemmas.Iterate
public import Std.Internal.ForIn

set_option linter.missingDocs true

@[expose] public section

/-!
# Hoare triple specifications for select functions

This module contains Hoare triple specifications for some functions in Core.
The specifications follow the `Triple x pre post epost` argument order, program first.
-/

namespace Std.Internal.Do

open Lean.Order

universe u v w w'
variable {m : Type u → Type v} {Pred : Type u} {EPred : Type u}

/-! # `Monad` -/

variable [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]

section MonadSpec
variable {Pred : Type w} {EPred : Type w'} [Assertion Pred] [Assertion EPred]
  [WPMonad m Pred EPred]

@[spec]
theorem Spec.pure (a : α) :
    Triple (Pure.pure (f := m) a) (post a) post epost :=
  Triple.pure a PartialOrder.rel_refl

@[spec]
theorem Spec.bind (x : m α) (f : α → m β) :
    Triple (x >>= f) (wp x (fun a => wp (f a) post epost) epost) post epost :=
  Triple.bind x f (fun a => wp (f a) post epost)
    (Triple.intro PartialOrder.rel_refl) (fun _ => Triple.intro PartialOrder.rel_refl)

@[spec]
theorem Spec.map (f : α → β) (x : m α) :
    Triple (f <$> x) (wp x (fun a => post (f a)) epost) post epost :=
  Triple.map f x (Triple.intro PartialOrder.rel_refl)

@[spec]
theorem Spec.seq (x : m (α → β)) (y : m α) :
    Triple (x <*> y) (wp x (fun f => wp y (fun a => post (f a)) epost) epost) post epost :=
  Triple.seq x y (Triple.intro PartialOrder.rel_refl)

end MonadSpec

/-! # `MonadLift` -/


@[spec]
theorem Spec.monadLift_StateT (x : m α) (post : α → σ → Pred) :
    Triple (MonadLift.monadLift x : StateT σ m α) (fun s => wp x (fun a => post a s) epost) post epost :=
  Triple.intro (WPMonad.le_wp_monadLift_StateT_apply x post)


@[spec]
theorem Spec.monadLift_ReaderT (x : m α) (post : α → ρ → Pred) :
    Triple (MonadLift.monadLift x : ReaderT ρ m α) (fun r => wp x (fun a => post a r) epost) post epost :=
  Triple.intro (by rw [WPMonad.wp_monadLift_ReaderT_apply_eq]; rfl)


@[spec]
theorem Spec.monadLift_ExceptT (x : m α) (post : α → Pred) (epost : EPost.Cons (ε → Pred) EPred) :
    Triple (MonadLift.monadLift x : ExceptT ε m α) (wp x post epost.tail) post epost :=
  Triple.intro (WPMonad.le_wp_monadLift_ExceptT_apply x post epost)


@[spec]
theorem Spec.monadLift_OptionT (x : m α) (post : α → Pred) (epost : EPost.Cons Pred EPred) :
    Triple (MonadLift.monadLift x : OptionT m α) (wp x post epost.tail) post epost :=
  Triple.intro (WPMonad.le_wp_monadLift_OptionT_apply x)

@[spec]
theorem Spec.monadLift_Id (x : Id α) :
    Triple (@MonadLiftT.monadLift Id m Id.instMonadLiftTOfPure α x) (post x.run) post epost :=
  Triple.pure x.run PartialOrder.rel_refl

/-! # `MonadLiftT` -/

omit [Monad m] in
theorem Spec.UnfoldLift.monadLift_trans [MonadLift n o] [MonadLiftT m n] (x : m α) :
    (MonadLiftT.monadLift x : o α) = MonadLift.monadLift (m := n) (monadLift x) := rfl

omit [Monad m] in
theorem Spec.UnfoldLift.monadLift_refl (x : m α) :
    (MonadLiftT.monadLift x : m α) = x := rfl

/-! # `MonadFunctor` -/

attribute [refl] PartialOrder.rel_refl


@[spec]
theorem Spec.monadMap_StateT
    (f : ∀{β}, m β → m β) {α} (x : StateT σ m α) (post : α → σ → Pred) :
    Triple (MonadFunctor.monadMap (m := m) f x : StateT σ m α)
      (fun s => wp (f (x.run s)) (fun (a, s') => post a s') epost) post epost :=
  Triple.intro (by rw [WPMonad.wp_monadMap_StateT_apply_eq]; rfl)


@[spec]
theorem Spec.monadMap_ReaderT
    (f : ∀{β}, m β → m β) {α} (x : ReaderT ρ m α) (post : α → ρ → Pred) :
    Triple (MonadFunctor.monadMap (m := m) f x : ReaderT ρ m α)
      (fun r => wp (f (x.run r)) (fun a => post a r) epost) post epost :=
  Triple.intro (by rw [WPMonad.wp_monadMap_ReaderT_apply_eq]; rfl)


@[spec]
theorem Spec.monadMap_ExceptT
    (f : ∀{β}, m β → m β) {α} (x : ExceptT ε m α) (post : α → Pred) (epost : EPost.Cons (ε → Pred) EPred) :
    Triple (MonadFunctor.monadMap (m := m) f x : ExceptT ε m α)
      (wp (f x.run) (epost.pushExcept post) epost.tail) post epost :=
  Triple.intro (by rw [WPMonad.wp_monadMap_ExceptT_apply_eq])


@[spec]
theorem Spec.monadMap_OptionT
    (f : ∀{β}, m β → m β) {α} (x : OptionT m α) (post : α → Pred) (epost : EPost.Cons Pred EPred) :
    Triple (MonadFunctor.monadMap (m := m) f x : OptionT m α)
      (wp (f x.run) (epost.pushOption post) epost.tail) post epost :=
  Triple.intro (by rw [WPMonad.wp_monadMap_OptionT_apply_eq])



@[spec]
theorem Spec.monadMap_refl (x : m α) :
    Triple (MonadFunctorT.monadMap f x : m α)
      (wp (f x : m α) post epost) post epost :=
  Triple.intro (by rw [WPMonad.wp_monadMap_refl_apply_eq])

/-! # `MonadControl` -/


@[spec]
theorem Spec.liftWith_StateT
    (f : (∀{β}, StateT σ m β → m (β × σ)) → m α) (post : α → σ → Pred) :
    Triple (MonadControl.liftWith (m:=m) f : StateT σ m α)
      (fun s => wp (f (fun x => x.run s)) (fun a => post a s) epost) post epost :=
  Triple.intro (by intro s; simp [WPMonad.wp_liftWith_StateT_apply_eq f]; apply WPMonad.map_le_wp_map'; ext; rfl)


@[spec]
theorem Spec.liftWith_ReaderT
    (f : (∀{β}, ReaderT ρ m β → m β) → m α) (post : α → ρ → Pred) :
    Triple (MonadControl.liftWith (m:=m) f : ReaderT ρ m α)
      (fun r => wp (f (fun x => x.run r)) (fun a => post a r) epost) post epost :=
  Triple.intro (by intro r; simp [WPMonad.wp_liftWith_ReaderT_apply_eq f]; rfl)


@[spec]
theorem Spec.liftWith_ExceptT
    (f : (∀{β}, ExceptT ε m β → m (Except ε β)) → m α) (post : α → Pred) (epost : EPost.Cons (ε → Pred) EPred) :
    Triple (MonadControl.liftWith (m:=m) f : ExceptT ε m α)
      (wp (f (fun x => x.run)) post epost.tail) post epost :=
  Triple.intro (by simp [WPMonad.wp_liftWith_ExceptT_apply_eq f]; apply WPMonad.map_le_wp_map'; ext; rfl)


@[spec]
theorem Spec.liftWith_OptionT
    (f : (∀{β}, OptionT m β → m (Option β)) → m α) (post : α → Pred) (epost : EPost.Cons Pred EPred) :
    Triple (MonadControl.liftWith (m:=m) f : OptionT m α)
      (wp (f (fun x => x.run)) post epost.tail) post epost :=
  Triple.intro (WPMonad.le_wp_liftWith_OptionT_apply f)


@[spec]
theorem Spec.restoreM_StateT (x : m (α × σ)) (post : α → σ → Pred) :
    Triple (MonadControl.restoreM (m:=m) x : StateT σ m α)
      (fun _ => wp x (fun (a, s) => post a s) epost) post epost :=
  Triple.intro (WPMonad.le_wp_restoreM_StateT_apply x)


@[spec]
theorem Spec.restoreM_ReaderT (x : m α) (post : α → ρ → Pred) :
    Triple (MonadControl.restoreM (m:=m) x : ReaderT ρ m α)
      (fun r => wp x (fun a => post a r) epost) post epost :=
  Triple.intro (by rw [WPMonad.wp_restoreM_ReaderT_apply_eq]; rfl)


@[spec]
theorem Spec.restoreM_ExceptT (x : m (@Except.{u, u} ε α)) (post : α → Pred) (epost : EPost.Cons (ε → Pred) EPred) :
    Triple (MonadControl.restoreM (m:=m) x : ExceptT ε m α)
      (wp x (epost.pushExcept post) epost.tail) post epost :=
  Triple.intro (by rw [WPMonad.wp_restoreM_ExceptT_apply_eq])


@[spec]
theorem Spec.restoreM_OptionT (x : m (Option α)) (post : α → Pred) (epost : EPost.Cons Pred EPred) :
    Triple (MonadControl.restoreM (m:=m) x : OptionT m α)
      (wp x (epost.pushOption post) epost.tail) post epost :=
  Triple.intro (by rw [WPMonad.wp_restoreM_OptionT_apply_eq])

/-! # `MonadControlT` -/



theorem Spec.liftWith_refl
    (f : (∀{β}, m β → m β) → m α) :
    Triple (MonadControlT.liftWith (m:=m) f : m α)
      (wp (f (fun x => x) : m α) post epost) post epost :=
  Triple.intro (by rw [WPMonad.wp_liftWith_refl_apply_eq])



theorem Spec.restoreM_refl (x : stM m m α) :
    Triple (MonadControlT.restoreM (m:=m) x : m α)
      (wp (Pure.pure x : m α) post epost) post epost :=
  Triple.intro (by rw [WPMonad.wp_restoreM_refl_apply_eq])

/-! # `ReaderT` -/


@[spec]
theorem Spec.read_ReaderT (post : ρ → ρ → Pred) :
    Triple (MonadReaderOf.read : ReaderT ρ m ρ)
      (fun r => post r r) post epost :=
  Triple.intro (by intro r; simpa [MonadReaderOf.read] using
    (WPMonad.pure_le_wp_pure (m := m) (x := r) (post := fun a => post a r) (epost := epost)))

theorem Spec.withReader_ReaderT (f : ρ → ρ) (x : ReaderT ρ m α) (post : α → ρ → Pred) :
    Triple (MonadWithReaderOf.withReader f x : ReaderT ρ m α)
      (fun r => wp x (fun a _ => post a r) epost (f r)) post epost :=
  Triple.intro (by rw [WPMonad.wp_withReader_ReaderT_apply_eq]; rfl)


theorem Spec.adapt_ReaderT (f : ρ → ρ') (x : ReaderT ρ' m α) (post : α → ρ → Pred) :
    Triple (ReaderT.adapt f x : ReaderT ρ m α)
      (fun r => wp x (fun a _ => post a r) epost (f r)) post epost :=
  Triple.intro (by rw [WPMonad.wp_adapt_ReaderT_apply_eq]; rfl)

/-! # `StateT` -/

section StateTSpec
variable {Pred : Type w} {EPred : Type w'} [Assertion Pred] [Assertion EPred]
  [WPMonad m Pred EPred] {epost : EPred}

@[spec]
theorem Spec.get_StateT (post : σ → σ → Pred) :
    Triple (MonadStateOf.get : StateT σ m σ)
      (fun s => post s s) post epost :=
  Triple.intro (by intro s; simpa [get_StateT] using!
    (WPMonad.pure_le_wp_pure (m := m) (x := (s, s))
      (post := fun x => post x.fst x.snd) (epost := epost)))


@[spec]
theorem Spec.set_StateT (s : σ) (post : PUnit → σ → Pred) :
    Triple (set s : StateT σ m PUnit)
      (fun _ => post ⟨⟩ s) post epost :=
  Triple.intro (by intro _; simpa [MonadStateOf.set] using!
    (WPMonad.pure_le_wp_pure (m := m) (x := (PUnit.unit, s))
      (post := fun x => post x.fst x.snd) (epost := epost)))


@[spec]
theorem Spec.modifyGet_StateT (f : σ → α × σ) (post : α → σ → Pred) :
    Triple (MonadStateOf.modifyGet f : StateT σ m α)
      (fun s => post (f s).1 (f s).2) post epost :=
  Triple.intro (by intro s; simpa [MonadStateOf.modifyGet] using!
    (WPMonad.pure_le_wp_pure (m := m) (x := f s)
      (post := fun x => post x.fst x.snd) (epost := epost)))

end StateTSpec

/-! # Lifting `MonadStateOf` -/

omit [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] in
theorem Spec.UnfoldLift.get [MonadLift m n] [MonadStateOf σ m] :
    (MonadStateOf.get : n σ) = monadLift (MonadStateOf.get : m σ) := rfl

omit [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] in
theorem Spec.UnfoldLift.set [MonadLift m n] [MonadStateOf σ m] (s : σ) :
    (MonadStateOf.set (m := n) s) = monadLift (MonadStateOf.set (m := m) s) := rfl

omit [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] in
theorem Spec.UnfoldLift.modifyGet [MonadLift m n] [MonadStateOf σ m] (f : σ → α × σ) :
    MonadStateOf.modifyGet (m := n) f = monadLift (MonadStateOf.modifyGet (m := m) f) := rfl

/-! # Lifting `MonadReaderOf` -/

omit [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] in
theorem Spec.UnfoldLift.read [MonadLift m n] [MonadReaderOf ρ m] :
    (MonadReaderOf.read : n ρ) = monadLift (MonadReaderOf.read : m ρ) := rfl

omit [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] in
theorem Spec.UnfoldLift.withReader [MonadFunctor m n] [MonadWithReaderOf ρ m] (f : ρ → ρ) :
    (MonadWithReaderOf.withReader f : n α → n α) = monadMap (m := m) (MonadWithReaderOf.withReader f) := rfl

/-! # `ExceptT` -/


@[spec]
theorem Spec.run_ExceptT (x : ExceptT ε m α) (post : α → Pred) (epost : EPost.Cons (ε → Pred) EPred) :
    Triple (x.run : m (@Except.{u, u} ε α))
      (wp x post epost)
      (epost.pushExcept post)
      epost.tail :=
  Triple.intro (by simp [PartialOrder.rel_refl])


@[spec]
theorem Spec.throw_ExceptT (err : ε) (post : α → Pred) (epost : EPost.Cons (ε → Pred) EPred) :
    Triple (MonadExceptOf.throw err : ExceptT ε m α) (epost.head err) post epost :=
  Triple.intro (by simpa [EPost.Cons.pushExcept] using!
    (WPMonad.pure_le_wp_pure (m := m) (x := Except.error err)
      (post := epost.pushExcept post)
      (epost := epost.tail)))


@[spec]
theorem Spec.tryCatch_ExceptT (x : ExceptT ε m α) (h : ε → ExceptT ε m α) (post : α → Pred) (epost : EPost.Cons (ε → Pred) EPred) :
    Triple (MonadExceptOf.tryCatch x h : ExceptT ε m α)
      (wp x post ⟨fun e => wp (h e) post epost, epost.tail⟩) post epost :=
  Triple.intro (WPMonad.le_wp_tryCatch_ExceptT_apply x h)


@[spec]
theorem Spec.orElse_ExceptT (x : ExceptT ε m α) (h : Unit → ExceptT ε m α) (post : α → Pred) (epost : EPost.Cons (ε → Pred) EPred) :
    Triple (OrElse.orElse x h : ExceptT ε m α)
      (wp x post ⟨fun _ => wp (h ()) post epost, epost.tail⟩) post epost :=
  Triple.intro (WPMonad.le_wp_orElse_ExceptT_apply x h)


@[spec]
theorem Spec.adapt_ExceptT (f : ε → ε') (x : ExceptT ε m α) (post : α → Pred) (epost : EPost.Cons (ε' → Pred) EPred) :
    Triple (ExceptT.adapt f x : ExceptT ε' m α)
      (wp x post ⟨fun e => epost.head (f e), epost.tail⟩) post epost :=
  Triple.intro (WPMonad.le_wp_adapt_ExceptT_apply f x)

/-! # `Except` -/


@[spec]
theorem Spec.throw_Except (err : ε) :
    Triple (MonadExceptOf.throw err : Except ε α) (epost.head err) post epost :=
  Triple.intro (by rw [WPMonad.wp_throw_Except_apply_eq]; rfl)


@[spec]
theorem Spec.tryCatch_Except (x : Except ε α) (h : ε → Except ε α) :
    Triple (MonadExceptOf.tryCatch x h : Except ε α)
      (wp x post epost⟨fun e => wp (h e) post epost⟩) post epost :=
  Triple.intro (by rw [WPMonad.wp_tryCatch_Except_apply_eq]; rfl)


@[spec]
theorem Spec.orElse_Except (x : Except ε α) (h : Unit → Except ε α) :
    Triple (OrElse.orElse x h : Except ε α)
      (wp x post epost⟨fun (_ : ε) => wp (h ()) post epost⟩) post epost :=
  Triple.intro (by simp only [wp, WP.wpTrans, OrElse.orElse, MonadExcept.orElse]; cases x <;> rfl)

/-! # `OptionT` -/


@[spec]
theorem Spec.run_OptionT (x : OptionT m α) (post : α → Pred) (epost : EPost.Cons Pred EPred) :
    Triple (x.run : m (Option α))
      (wp x post epost)
      (epost.pushOption post)
      epost.tail :=
  Triple.intro (by rw [← OptionT.wp_apply_eq])


@[spec]
theorem Spec.throw_OptionT (err : PUnit) (post : α → Pred) (epost : EPost.Cons Pred EPred) :
    Triple (MonadExceptOf.throw err : OptionT m α) epost.head post epost :=
  Triple.intro (WPMonad.le_wp_throw_OptionT_apply err)


@[spec]
theorem Spec.tryCatch_OptionT (x : OptionT m α) (h : PUnit → OptionT m α) (post : α → Pred) (epost : EPost.Cons Pred EPred) :
    Triple (MonadExceptOf.tryCatch x h : OptionT m α)
      (wp x post ⟨wp (h ⟨⟩) post epost, epost.tail⟩) post epost :=
  Triple.intro (WPMonad.le_wp_tryCatch_OptionT_apply x h)


@[spec]
theorem Spec.orElse_OptionT (x : OptionT m α) (h : Unit → OptionT m α) (post : α → Pred) (epost : EPost.Cons Pred EPred) :
    Triple (OrElse.orElse x h : OptionT m α)
      (wp x post ⟨wp (h ()) post epost, epost.tail⟩) post epost :=
  Triple.intro (WPMonad.le_wp_orElse_OptionT_apply x h)

/-! # `Option` -/


@[spec]
theorem Spec.throw_Option (err : PUnit) :
    Triple (MonadExceptOf.throw err : Option α) epost post epost :=
  Triple.intro (by rw [WPMonad.wp_throw_Option_apply_eq]; rfl)


@[spec]
theorem Spec.tryCatch_Option (x : Option α) (h : PUnit → Option α) :
    Triple (MonadExceptOf.tryCatch x h : Option α)
      (wp x post (wp (h ⟨⟩) post epost)) post epost :=
  Triple.intro (by rw [WPMonad.wp_tryCatch_Option_apply_eq]; rfl)


@[spec]
theorem Spec.orElse_Option (x : Option α) (h : Unit → Option α) (post : α → Prop) (epost : Prop) :
    Triple (OrElse.orElse x h : Option α)
      (wp x post (wp (h ()) post epost)) post epost :=
  Triple.intro (by rw [WPMonad.wp_orElse_Option_apply_eq]; rfl)

/-! # `EStateM` -/


@[spec]
theorem Spec.get_EStateM (post : σ → σ → Prop) (epost : ε → σ → Prop) :
    Triple (MonadStateOf.get : EStateM ε σ σ)
      (fun s => post s s) post epost :=
  Triple.intro (by rw [WPMonad.wp_get_EStateM_apply_eq]; rfl)


@[spec]
theorem Spec.set_EStateM (s : σ) (post : PUnit → σ → Prop) (epost : ε → σ → Prop) :
    Triple (MonadStateOf.set s : EStateM ε σ PUnit)
      (fun _ => post ⟨⟩ s) post epost :=
  Triple.intro (by rw [WPMonad.wp_set_EStateM_apply_eq]; rfl)


@[spec]
theorem Spec.modifyGet_EStateM (f : σ → α × σ) (post : α → σ → Prop) (epost : ε → σ → Prop) :
    Triple (MonadStateOf.modifyGet f : EStateM ε σ α)
      (fun s => post (f s).1 (f s).2) post epost :=
  Triple.intro (by rw [WPMonad.wp_modifyGet_EStateM_apply_eq]; rfl)


@[spec]
theorem Spec.throw_EStateM (err : ε) (post : α → σ → Prop) (epost : ε → σ → Prop) :
    Triple (MonadExceptOf.throw err : EStateM ε σ α) (epost err) post epost :=
  Triple.intro (by rw [WPMonad.wp_throw_EStateM_apply_eq]; rfl)


@[spec]
theorem Spec.tryCatch_EStateM (x : EStateM ε σ α) (h : ε → EStateM ε σ α)
    (post : α → σ → Prop) (epost : ε → σ → Prop) :
    Triple (MonadExceptOf.tryCatch x h : EStateM ε σ α)
      (fun s => wp x post (fun e s' => wp (h e) post epost s') s) post epost :=
  Triple.intro (by rw [WPMonad.wp_tryCatch_EStateM_apply_eq]; rfl)


theorem Spec.orElse_EStateM (x : EStateM ε σ α) (h : Unit → EStateM ε σ α)
    (post : α → σ → Prop) (epost : ε → σ → Prop) :
    Triple (OrElse.orElse x h : EStateM ε σ α)
      (fun s => wp x post (fun _ s' => wp (h ()) post epost s') s) post epost :=
  Triple.intro (by rw [WPMonad.wp_orElse_EStateM_apply_eq]; rfl)


theorem Spec.adaptExcept_EStateM (f : ε → ε') (x : EStateM ε σ α)
    (post : α → σ → Prop) (epost : ε' → σ → Prop) :
    Triple (EStateM.adaptExcept f x : EStateM ε' σ α)
      (wp x post (fun e => epost (f e))) post epost :=
  Triple.intro (by rw [WPMonad.wp_adaptExcept_EStateM_apply_eq]; rfl)

/-! # Lifting `MonadExceptOf` -/



@[spec]
theorem Spec.throw_MonadExcept [MonadExceptOf ε m] (err : ε) :
    Triple (throw err : m α)
      (wp (MonadExceptOf.throw err : m α) post epost) post epost :=
  Triple.intro (by simp [throw, PartialOrder.rel_refl])



theorem Spec.tryCatch_MonadExcept [MonadExceptOf ε m] (x : m α) (h : ε → m α) :
    Triple (tryCatch x h : m α)
      (wp (MonadExceptOf.tryCatch x h : m α) post epost) post epost :=
  Triple.intro (by rw [WPMonad.wp_tryCatch_MonadExcept_apply_eq])


@[spec]
theorem Spec.throw_ReaderT [MonadExceptOf ε m] (err : ε) (post : α → ρ → Pred) :
    Triple (MonadExceptOf.throw (ε:=ε) err : ReaderT ρ m α)
      (wp (MonadLift.monadLift (MonadExceptOf.throw (ε:=ε) err : m α) : ReaderT ρ m α) post epost) post epost :=
  Triple.intro (by rw [WPMonad.wp_throw_ReaderT_lift_apply_eq]; rfl)


@[spec]
theorem Spec.throw_StateT [MonadExceptOf ε m] (err : ε) (post : α → σ → Pred) :
    Triple (MonadExceptOf.throw (ε:=ε) err : StateT σ m α)
      (wp (MonadLift.monadLift (MonadExceptOf.throw (ε:=ε) err : m α) : StateT σ m α) post epost) post epost :=
  Triple.intro (by rw [WPMonad.wp_throw_StateT_lift_apply_eq]; rfl)


@[spec]
theorem Spec.throw_ExceptT_lift [MonadExceptOf ε m] (err : ε) (post : α → Pred) (epost : EPost.Cons (ε' → Pred) EPred) :
    Triple (MonadExceptOf.throw (ε:=ε) err : ExceptT ε' m α)
      (wp (MonadExceptOf.throw (ε:=ε) err : m (@Except.{u, u} ε' α))
        (fun r => match r with | .ok a => post a | .error e => epost.head e) epost.tail) post epost :=
  Triple.intro (by rw [WPMonad.wp_throw_lift_ExceptT_apply_eq]; apply WP.wp_consequence; intro r; cases r <;> rfl)


@[spec]
theorem Spec.throw_Option_lift [MonadExceptOf ε m] (err : ε) (post : α → Pred) (epost : EPost.Cons Pred EPred) :
    Triple (MonadExceptOf.throw (ε:=ε) err : OptionT m α)
      (wp (MonadExceptOf.throw (ε:=ε) err : m (Option α))
        (epost.pushOption post) epost.tail) post epost :=
  Triple.intro (by rw [WPMonad.wp_throw_lift_OptionT_apply_eq])


@[spec]
theorem Spec.tryCatch_ReaderT [MonadExceptOf ε m] (x : ReaderT ρ m α) (h : ε → ReaderT ρ m α)
    (post : α → ρ → Pred) :
    Triple (MonadExceptOf.tryCatch (ε:=ε) x h : ReaderT ρ m α)
      (fun r => wp (MonadExceptOf.tryCatch (ε:=ε) (x.run r) (fun e => (h e).run r) : m α)
        (fun a => post a r) epost) post epost :=
  Triple.intro (by rw [WPMonad.wp_tryCatch_ReaderT_lift_apply_eq]; rfl)


@[spec]
theorem Spec.tryCatch_StateT [MonadExceptOf ε m] (x : StateT σ m α) (h : ε → StateT σ m α)
    (post : α → σ → Pred) :
    Triple (MonadExceptOf.tryCatch (ε:=ε) x h : StateT σ m α)
      (fun s => wp (MonadExceptOf.tryCatch (ε:=ε) (x.run s) (fun e => (h e).run s) : m (α × σ))
        (fun (a, s') => post a s') epost) post epost :=
  Triple.intro (by rw [WPMonad.wp_tryCatch_StateT_lift_apply_eq]; rfl)


@[spec]
theorem Spec.tryCatch_ExceptT_lift [MonadExceptOf ε m] (x : ExceptT ε' m α) (h : ε → ExceptT ε' m α)
    (post : α → Pred) (epost : EPost.Cons (ε' → Pred) EPred) :
    Triple (MonadExceptOf.tryCatch (ε:=ε) x h : ExceptT ε' m α)
      (wp (MonadExceptOf.tryCatch (ε:=ε) x h : m (@Except.{u, u} ε' α))
        (fun | .ok a => post a | .error e => epost.head e) epost.tail) post epost :=
  Triple.intro (by rw [WPMonad.wp_tryCatch_lift_ExceptT_apply_eq]; apply WP.wp_consequence; intro r; cases r <;> rfl)


@[spec]
theorem Spec.tryCatch_OptionT_lift [MonadExceptOf ε m] (x : OptionT m α) (h : ε → OptionT m α)
    (post : α → Pred) (epost : EPost.Cons Pred EPred) :
    Triple (MonadExceptOf.tryCatch (ε:=ε) x h : OptionT m α)
      (wp (MonadExceptOf.tryCatch (ε:=ε) x h : m (Option α))
        (epost.pushOption post) epost.tail) post epost :=
  Triple.intro (by rw [WPMonad.wp_tryCatch_lift_OptionT_apply_eq])

-- /-! # `MonadFunctorT` / `MonadControlT` transitivity -/



@[spec]
theorem Spec.monadMap_trans
    {n₁ : Type u → Type v} {n₂ : Type u → Type v}
    [MonadFunctor n₁ m] [MonadFunctorT n₂ n₁]
    {f : ∀{β}, n₂ β → n₂ β}
    (x : m α) :
    Triple (MonadFunctorT.monadMap (m:=n₂) f x : m α)
      (wp (MonadFunctor.monadMap (m:=n₁) (MonadFunctorT.monadMap (m:=n₂) f) x : m α) post epost) post epost :=
  Triple.intro (by rw [WPMonad.wp_monadMap_trans_apply_eq])



@[spec]
theorem Spec.liftWith_trans
    {n₁ : Type u → Type v} {n₂ : Type u → Type v}
    [MonadControl n₁ m] [MonadControlT n₂ n₁]
    (f : (∀{β}, m β → n₂ (stM n₂ m β)) → n₂ α) :
    Triple (MonadControlT.liftWith (m:=n₂) f : m α)
      (wp (MonadControl.liftWith (m:=n₁) fun x₂ => MonadControlT.liftWith fun x₁ => f (x₁ ∘ x₂) : m α) post epost) post epost :=
  Triple.intro (by rw [WPMonad.wp_liftWith_trans_apply_eq])


@[spec]
theorem Spec.restoreM_trans
    {n₁ : Type u → Type v} {n₂ : Type u → Type v}
    [MonadControl n₁ m] [MonadControlT n₂ n₁]
    (x : stM n₂ m α) :
    Triple (MonadControlT.restoreM (m:=n₂) x : m α)
      (wp (MonadControl.restoreM (m:=n₁) (MonadControlT.restoreM (m:=n₂) x) : m α) post epost) post epost :=
  Triple.intro (by rw [WPMonad.wp_restoreM_trans_apply_eq])

end Std.Internal.Do

-- /-! # `ForIn` -/

namespace Std.Internal.Do

open Lean.Order

universe u₁ u₂ v w uₚ uₑ

variable {α : Type u₁} {β : Type u₂} {m : Type u₂ → Type v} {Pred : Type uₚ} {EPred : Type uₑ}
variable [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]

/-- The type of loop invariants used by the specifications of `for ... in ...` loops.
A loop invariant maps the elements consumed so far, the elements remaining, and the accumulator
state to an assertion. -/
@[spec_invariant_type, simp, grind =]
def Invariant (α : Type u₁) (β : Type u₂) (Pred : Type uₚ) :=
  List α → List α → β → Pred

/-- An invariant combinator for loops with early return, for the new `do` elaborator which
uses `Prod` for the state tuple: `onContinue` is the invariant while iterating, `onReturn`
holds once the loop returned early with a value. -/
noncomputable abbrev Invariant.withEarlyReturnNewDo {α : Type u₁} {β : Type u₂}
    {γ : Type u₂} (Pred) [Assertion Pred]
    (onContinue : List α → List α → β → Pred)
    (onReturn : γ → β → Pred) :
    Invariant α (Option γ × β) Pred :=
  fun pref suff ⟨x, b⟩ =>
        (⌜x = none⌝ ⊓ onContinue pref suff b)
      ⊔ (iSup fun r => ⌜x = some r ∧ suff = []⌝ ⊓ onReturn r b)

@[spec]
theorem Spec.forIn'_list
    {xs : List α} {init : β} {f : (a : α) → a ∈ xs → β → m (ForInStep β)}
    (inv : Invariant α β Pred)
    {epost : EPred}
    (step : ∀ pref cur suff (h : xs = pref ++ cur :: suff) b,
      Triple
        (f cur (by simp [h]) b)
        (inv pref (cur::suff) b)
        (fun r => match r with
                 | .yield b' => inv (pref ++ [cur]) suff b'
                 | .done b' => inv xs [] b')
        epost) :
    Triple
      (forIn' xs init f)
      (inv [] xs init)
      (fun b => inv xs [] b)
      epost := by
  suffices h : ∀ pref suff (hxs : xs = pref ++ suff),
      Triple
        (forIn' (m:=m) suff init (fun a ha => f a (by simp [hxs, ha])))
        (inv pref suff init)
        (fun b => inv xs [] b)
        epost
    from h [] xs rfl
  intro pref suff hxs
  induction suff generalizing pref init
  case nil => apply Triple.pure; simp [hxs]; rfl
  case cons x suff ih =>
    simp only [List.forIn'_cons]
    apply Triple.bind
    case hx => exact step _ _ _ hxs init
    case hf =>
      intro r
      split
      next b => -- .done case
        apply Triple.pure; rfl
      next b => -- .yield case
        simp
        exact @ih b (pref ++ [x]) (by simp [hxs])


theorem Spec.forIn'_list_const_inv
    {xs : List α} {init : β} {f : (a : α) → a ∈ xs → β → m (ForInStep β)}
    {inv : (β → Pred)}
    {epost : EPred}
    (step : ∀ x (hx : x ∈ xs) b,
      Triple
        (f x hx b)
        (inv b)
        (fun r => match r with | .yield b' => inv b' | .done b' => inv b')
        epost) :
    Triple (forIn' xs init f) (inv init) inv epost :=
  Spec.forIn'_list (fun _ _ b => inv b)
    (fun _p c _s h b => step c (by rw [h]; exact List.mem_append_right _ (List.Mem.head _)) b)



@[spec]
theorem Spec.forIn_list
    {xs : List α} {init : β} {f : α → β → m (ForInStep β)}
    (inv : Invariant α β Pred)
    {epost : EPred}
    (step : ∀ pref cur suff (_h : xs = pref ++ cur :: suff) b,
      Triple
        (f cur b)
        (inv pref (cur::suff) b)
        (fun r => match r with
          | .yield b' => inv (pref ++ [cur]) suff b'
          | .done b' => inv xs [] b')
        epost) :
    Triple
      (forIn xs init f)
      (inv [] xs init)
      (fun b => inv xs [] b)
      epost := by
  simp only [← forIn'_eq_forIn]
  exact Spec.forIn'_list inv step

theorem Spec.forIn_list_const_inv
    {xs : List α} {init : β} {f : α → β → m (ForInStep β)}
    {inv : (β → Pred)}
    {epost : EPred}
    (step : ∀ hd b,
      Triple
        (f hd b)
        (inv b)
        (fun r => match r with | .yield b' => inv b' | .done b' => inv b')
        epost) :
    Triple (forIn xs init f) (inv init) inv epost :=
  Spec.forIn_list (fun _ _ b => inv b) (fun _p c _s _h b => step c b)


@[spec]
theorem Spec.foldlM_list
    {xs : List α} {init : β} {f : β → α → m β}
    (inv : Invariant α β Pred)
    {epost : EPred}
    (step : ∀ pref cur suff (_h : xs = pref ++ cur :: suff) b,
      Triple
        (f b cur)
        (inv pref (cur::suff) b)
        (fun b' => inv (pref ++ [cur]) suff b')
        epost) :
    Triple
      (List.foldlM f init xs)
      (inv [] xs init)
      (fun b => inv xs [] b)
      epost := by
  have : xs.foldlM f init = forIn xs init (fun a b => ForInStep.yield <$> f b a) := by
    simp [List.forIn_yield_eq_foldlM, id_map']
  rw [this]
  apply Spec.forIn_list inv
  intros
  apply Triple.map
  apply step <;> assumption


theorem Spec.foldlM_list_const_inv
    {xs : List α} {init : β} {f : β → α → m β}
    {inv : (β → Pred)}
    {epost : EPred}
    (step : ∀ hd b,
      Triple
        (f b hd)
        (inv b)
        (fun b' => inv b')
        epost) :
    Triple (List.foldlM f init xs) (inv init) inv epost :=
    Spec.foldlM_list (fun _ _ b => inv b) (fun _p c _s _h b => step c b)


/-- Every container with a `PureForIn'` instance iterates over `ForIn.toList`, so one specification
covers them all. -/
@[spec low+10]
theorem Spec.forIn'_pure {ρ : Type w} {d : Membership α ρ} [ForIn' m ρ α d] [ForIn Id ρ α]
    [LawfulMemForInId ρ α] [PureForIn' m ρ α]
    {xs : ρ} {init : β} {f : (a : α) → a ∈ xs → β → m (ForInStep β)}
    (inv : Invariant α β Pred)
    {epost : EPred}
    (step : ∀ pref cur suff (h : ForIn.toList xs = pref ++ cur :: suff) b,
      Triple (f cur ((LawfulMemForInId.mem_toList_iff).mp (by simp [h])) b)
        (inv pref (cur :: suff) b)
        (fun r => match r with
          | .yield b' => inv (pref ++ [cur]) suff b'
          | .done b' => inv (ForIn.toList xs) [] b')
        epost) :
    Triple (forIn' xs init f) (inv [] (ForIn.toList xs) init)
      (fun b => inv (ForIn.toList xs) [] b) epost := by
  rw [PureForIn'.forIn'_eq]
  exact Spec.forIn'_list inv step

/-- Every container with a `PureForIn` instance iterates over `ForIn.toList`, so one specification
covers them all. -/
@[spec low+10]
theorem Spec.forIn_pure {ρ : Type w} [ForIn m ρ α] [ForIn Id ρ α] [PureForIn m ρ α]
    {xs : ρ} {init : β} {f : α → β → m (ForInStep β)}
    (inv : Invariant α β Pred)
    {epost : EPred}
    (step : ∀ pref cur suff (_h : ForIn.toList xs = pref ++ cur :: suff) b,
      Triple (f cur b)
        (inv pref (cur :: suff) b)
        (fun r => match r with
          | .yield b' => inv (pref ++ [cur]) suff b'
          | .done b' => inv (ForIn.toList xs) [] b')
        epost) :
    Triple (forIn xs init f) (inv [] (ForIn.toList xs) init)
      (fun b => inv (ForIn.toList xs) [] b) epost := by
  rw [PureForIn.forIn_eq]
  exact Spec.forIn_list inv step


section Iterators
open Std Std.Iterators


@[spec low]
theorem Spec.foldM_iter {α β γ : Type u} {m : Type u → Type w} {Pred : Type uₚ} {EPred : Type uₑ}
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    [Iterator α Id β] [Finite α Id] [IteratorLoop α Id m] [LawfulIteratorLoop α Id m]
    {it : Iter (α := α) β}
    {init : γ} {f : γ → β → m γ}
    (inv : Invariant β γ Pred)
    {epost : EPred}
    (step : ∀ pref cur suff (_h : it.toList = pref ++ cur :: suff) b,
      Triple
        (f b cur)
        (inv pref (cur::suff) b)
        (fun b' => inv (pref ++ [cur]) suff b')
        epost) :
    Triple (it.foldM f init) (inv [] it.toList init)
      (fun b => inv it.toList [] b) epost := by
  rw [← Iter.foldlM_toList]
  exact Spec.foldlM_list inv step


@[spec low]
theorem Spec.foldM_iterM_id {α β γ : Type u} {m : Type u → Type w} {Pred : Type uₚ} {EPred : Type uₑ}
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    [Iterator α Id β] [Finite α Id] [IteratorLoop α Id m] [LawfulIteratorLoop α Id m]
    {it : IterM (α := α) Id β}
    {init : γ} {f : γ → β → m γ}
    (inv : Invariant β γ Pred)
    {epost : EPred}
    (step : ∀ pref cur suff (_h : it.toList.run = pref ++ cur :: suff) b,
      Triple
        (f b cur)
        (inv pref (cur::suff) b)
        (fun b' => inv (pref ++ [cur]) suff b')
        epost) :
    Triple (it.foldM f init) (inv [] it.toList.run init)
      (fun b => inv it.toList.run [] b) epost := by
  rw [← IterM.foldlM_toList]
  exact Spec.foldlM_list inv step


@[spec]
theorem Spec.IterM.forIn_filterMapWithPostcondition {α β β₂ γ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    {Pred : Type uₚ} {EPred : Type uₑ}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] [Monad o] [Assertion Pred] [Assertion EPred] [WPMonad o Pred EPred]
    [MonadLiftT m n] [LawfulMonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m]
    [IteratorLoop α m o] [LawfulIteratorLoop α m o]
    {it : IterM (α := α) m β} {f : β → PostconditionT n (Option β₂)} {init : γ}
    {g : β₂ → γ → o (ForInStep γ)} {P : Pred} {Q : γ → Pred} {eQ : EPred}
    (h :
        haveI : MonadLift n o := ⟨monadLift⟩
        Triple (forIn (m := o) it init (fun out acc => do
          match ← (f out).run with
          | some c => g c acc
          | none => return .yield acc)) P Q eQ) :
    Triple (forIn (it.filterMapWithPostcondition f) init g) P Q eQ := by
  rwa [Std.IterM.forIn_filterMapWithPostcondition]


@[spec]
theorem Spec.IterM.forIn_filterMapM {α β β₂ γ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    {Pred : Type uₚ} {EPred : Type uₑ}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] [Monad o] [Assertion Pred] [Assertion EPred] [WPMonad o Pred EPred]
    [MonadAttach n] [WeaklyLawfulMonadAttach n]
    [MonadLiftT m n] [LawfulMonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m]
    [IteratorLoop α m o] [LawfulIteratorLoop α m o]
    {it : IterM (α := α) m β} {f : β → n (Option β₂)} {init : γ} {g : β₂ → γ → o (ForInStep γ)}
    {P : Pred} {Q : γ → Pred} {eQ : EPred}
    (h :
        haveI : MonadLift n o := ⟨monadLift⟩
        Triple (forIn (m := o) it init (fun out acc => do
          match ← f out with
          | some c => g c acc
          | none => return .yield acc)) P Q eQ) :
    Triple (forIn (it.filterMapM f) init g) P Q eQ := by
  rwa [Std.IterM.forIn_filterMapM]


@[spec]
theorem Spec.IterM.forIn_filterMap {α β β₂ γ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''}
    {Pred : Type uₚ} {EPred : Type uₑ}
    [Monad m] [LawfulMonad m] [Monad n] [Assertion Pred] [Assertion EPred] [WPMonad n Pred EPred]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    [Iterator α m β] [Finite α m]
    [IteratorLoop α m n] [LawfulIteratorLoop α m n]
    {it : IterM (α := α) m β} {f : β → Option β₂} {init : γ} {g : β₂ → γ → n (ForInStep γ)}
    {P : Pred} {Q : γ → Pred} {eQ : EPred}
    (h : Triple (forIn it init (fun out acc => do
          match f out with
          | some c => g c acc
          | none => return .yield acc)) P Q eQ) :
    Triple (forIn (it.filterMap f) init g) P Q eQ := by
  rwa [Std.IterM.forIn_filterMap]


@[spec]
theorem Spec.IterM.forIn_mapWithPostcondition {α β β₂ γ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    {Pred : Type uₚ} {EPred : Type uₑ}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] [Monad o] [Assertion Pred] [Assertion EPred] [WPMonad o Pred EPred]
    [MonadLiftT m n] [LawfulMonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m]
    [IteratorLoop α m o] [LawfulIteratorLoop α m o]
    {it : IterM (α := α) m β} {f : β → PostconditionT n β₂} {init : γ}
    {g : β₂ → γ → o (ForInStep γ)} {P : Pred} {Q : γ → Pred} {eQ : EPred}
    (h :
        haveI : MonadLift n o := ⟨monadLift⟩
        Triple (forIn (m := o) it init (fun out acc => do g (← (f out).run) acc)) P Q eQ) :
    Triple (forIn (it.mapWithPostcondition f) init g) P Q eQ := by
  rwa [Std.IterM.forIn_mapWithPostcondition]


@[spec]
theorem Spec.IterM.forIn_mapM {α β β₂ γ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    {Pred : Type uₚ} {EPred : Type uₑ}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] [Monad o] [Assertion Pred] [Assertion EPred] [WPMonad o Pred EPred]
    [MonadAttach n] [WeaklyLawfulMonadAttach n]
    [MonadLiftT m n] [LawfulMonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m]
    [IteratorLoop α m o] [LawfulIteratorLoop α m o]
    {it : IterM (α := α) m β} {f : β → n β₂} {init : γ} {g : β₂ → γ → o (ForInStep γ)}
    {P : Pred} {Q : γ → Pred} {eQ : EPred}
    (h :
        haveI : MonadLift n o := ⟨monadLift⟩
        Triple (forIn (m := o) it init (fun out acc => do g (← f out) acc)) P Q eQ) :
    Triple (forIn (it.mapM f) init g) P Q eQ := by
  rwa [Std.IterM.forIn_mapM]


@[spec]
theorem Spec.IterM.forIn_map {α β β₂ γ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''}
    {Pred : Type uₚ} {EPred : Type uₑ}
    [Monad m] [LawfulMonad m] [Monad n] [Assertion Pred] [Assertion EPred] [WPMonad n Pred EPred]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    [Iterator α m β] [Finite α m] [IteratorLoop α m n] [LawfulIteratorLoop α m n]
    {it : IterM (α := α) m β} {f : β → β₂} {init : γ} {g : β₂ → γ → n (ForInStep γ)}
    {P : Pred} {Q : γ → Pred} {eQ : EPred}
    (h : Triple (forIn it init (fun out acc => do g (f out) acc)) P Q eQ) :
    Triple (forIn (it.map f) init g) P Q eQ := by
  rwa [Std.IterM.forIn_map]


@[spec]
theorem Spec.IterM.forIn_filterWithPostcondition {α β γ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    {Pred : Type uₚ} {EPred : Type uₑ}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] [Monad o] [Assertion Pred] [Assertion EPred] [WPMonad o Pred EPred]
    [MonadLiftT m n] [LawfulMonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m]
    [IteratorLoop α m o] [LawfulIteratorLoop α m o]
    {it : IterM (α := α) m β} {f : β → PostconditionT n (ULift Bool)} {init : γ}
    {g : β → γ → o (ForInStep γ)} {P : Pred} {Q : γ → Pred} {eQ : EPred}
    (h :
        haveI : MonadLift n o := ⟨monadLift⟩
        Triple (forIn (m := o) it init (fun out acc => do if (← (f out).run).down then g out acc else return .yield acc)) P Q eQ) :
    Triple (forIn (it.filterWithPostcondition f) init g) P Q eQ := by
  rwa [Std.IterM.forIn_filterWithPostcondition]


@[spec]
theorem Spec.IterM.forIn_filterM {α β γ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    {Pred : Type uₚ} {EPred : Type uₑ}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] [Monad o] [Assertion Pred] [Assertion EPred] [WPMonad o Pred EPred]
    [MonadAttach n] [WeaklyLawfulMonadAttach n]
    [MonadLiftT m n] [LawfulMonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m]
    [IteratorLoop α m o] [LawfulIteratorLoop α m o]
    {it : IterM (α := α) m β} {f : β → n (ULift Bool)} {init : γ} {g : β → γ → o (ForInStep γ)}
    {P : Pred} {Q : γ → Pred} {eQ : EPred}
    (h :
        haveI : MonadLift n o := ⟨monadLift⟩
        Triple (forIn (m := o) it init (fun out acc => do if (← f out).down then g out acc else return .yield acc)) P Q eQ) :
    Triple (forIn (it.filterM f) init g) P Q eQ := by
  rwa [Std.IterM.forIn_filterM]


@[spec]
theorem Spec.IterM.forIn_filter {α β γ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''}
    {Pred : Type uₚ} {EPred : Type uₑ}
    [Monad m] [LawfulMonad m] [Monad n] [Assertion Pred] [Assertion EPred] [WPMonad n Pred EPred]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    [Iterator α m β] [Finite α m] [IteratorLoop α m n] [LawfulIteratorLoop α m n]
    {it : IterM (α := α) m β} {f : β → Bool} {init : γ} {g : β → γ → n (ForInStep γ)}
    {P : Pred} {Q : γ → Pred} {eQ : EPred}
    (h : Triple (forIn (m := n) it init (fun out acc => do if f out then g out acc else return .yield acc)) P Q eQ) :
    Triple (forIn (it.filter f) init g) P Q eQ := by
  rwa [Std.IterM.forIn_filter]


@[spec]
theorem Spec.IterM.foldM_filterMapWithPostcondition {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    {Pred : Type uₚ} {EPred : Type uₑ}
    [Iterator α m β] [Finite α m]
    [Monad m] [Monad n] [Monad o] [LawfulMonad m] [LawfulMonad n] [Assertion Pred] [Assertion EPred] [WPMonad o Pred EPred]
    [IteratorLoop α m n] [IteratorLoop α m o]
    [LawfulIteratorLoop α m n] [LawfulIteratorLoop α m o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    {f : β → PostconditionT n (Option γ)} {g : δ → γ → o δ} {init : δ} {it : IterM (α := α) m β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h :
        haveI : MonadLift n o := ⟨MonadLiftT.monadLift⟩
        Triple (it.foldM (n := o) (init := init) (fun d b => do
          let some c ← (f b).run | Pure.pure d
          g d c)) P Q eQ) :
    Triple ((it.filterMapWithPostcondition f).foldM (init := init) g) P Q eQ := by
  rwa [Std.IterM.foldM_filterMapWithPostcondition]


@[spec]
theorem Spec.IterM.foldM_filterMapM {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    {Pred : Type uₚ} {EPred : Type uₑ}
    [Iterator α m β] [Finite α m]
    [Monad m] [LawfulMonad m]
    [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [Monad o] [Assertion Pred] [Assertion EPred] [WPMonad o Pred EPred]
    [IteratorLoop α m n] [IteratorLoop α m o]
    [LawfulIteratorLoop α m n] [LawfulIteratorLoop α m o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    {f : β → n (Option γ)} {g : δ → γ → o δ} {init : δ} {it : IterM (α := α) m β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h :
        haveI : MonadLift n o := ⟨MonadLiftT.monadLift⟩
        Triple (it.foldM (n := o) (init := init) (fun d b => do
          let some c ← f b | Pure.pure d
          g d c)) P Q eQ) :
    Triple ((it.filterMapM f).foldM (init := init) g) P Q eQ := by
  rwa [Std.IterM.foldM_filterMapM]


@[spec]
theorem Spec.IterM.foldM_mapWithPostcondition {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    {Pred : Type uₚ} {EPred : Type uₑ}
    [Iterator α m β] [Finite α m]
    [Monad m] [Monad n] [Monad o] [LawfulMonad m] [LawfulMonad n] [Assertion Pred] [Assertion EPred] [WPMonad o Pred EPred]
    [IteratorLoop α m n] [IteratorLoop α m o]
    [LawfulIteratorLoop α m n] [LawfulIteratorLoop α m o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    {f : β → PostconditionT n γ} {g : δ → γ → o δ} {init : δ} {it : IterM (α := α) m β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h :
        haveI : MonadLift n o := ⟨MonadLiftT.monadLift⟩
        Triple (it.foldM (n := o) (init := init) (fun d b => do let c ← (f b).run; g d c)) P Q eQ) :
    Triple ((it.mapWithPostcondition f).foldM (init := init) g) P Q eQ := by
  rwa [Std.IterM.foldM_mapWithPostcondition]


@[spec]
theorem Spec.IterM.foldM_mapM {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    {Pred : Type uₚ} {EPred : Type uₑ}
    [Iterator α m β] [Finite α m]
    [Monad m] [LawfulMonad m]
    [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [Monad o] [Assertion Pred] [Assertion EPred] [WPMonad o Pred EPred]
    [IteratorLoop α m n] [IteratorLoop α m o]
    [LawfulIteratorLoop α m n] [LawfulIteratorLoop α m o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    {f : β → n γ} {g : δ → γ → o δ} {init : δ} {it : IterM (α := α) m β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h :
        haveI : MonadLift n o := ⟨MonadLiftT.monadLift⟩
        Triple (it.foldM (n := o) (init := init) (fun d b => do let c ← f b; g d c)) P Q eQ) :
    Triple ((it.mapM f).foldM (init := init) g) P Q eQ := by
  rwa [Std.IterM.foldM_mapM]


@[spec]
theorem Spec.IterM.foldM_filterWithPostcondition {α β δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    {Pred : Type uₚ} {EPred : Type uₑ}
    [Iterator α m β] [Finite α m]
    [Monad m] [Monad n] [Monad o] [LawfulMonad m] [LawfulMonad n] [Assertion Pred] [Assertion EPred] [WPMonad o Pred EPred]
    [IteratorLoop α m n] [IteratorLoop α m o]
    [LawfulIteratorLoop α m n] [LawfulIteratorLoop α m o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    {f : β → PostconditionT n (ULift Bool)} {g : δ → β → o δ} {init : δ} {it : IterM (α := α) m β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h :
        haveI : MonadLift n o := ⟨MonadLiftT.monadLift⟩
        Triple (it.foldM (n := o) (init := init) (fun d b => do if (← (f b).run).down then g d b else Pure.pure d)) P Q eQ) :
    Triple ((it.filterWithPostcondition f).foldM (init := init) g) P Q eQ := by
  rwa [Std.IterM.foldM_filterWithPostcondition]


@[spec]
theorem Spec.IterM.foldM_filterM {α β δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    {Pred : Type uₚ} {EPred : Type uₑ}
    [Iterator α m β] [Finite α m]
    [Monad m] [LawfulMonad m]
    [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [Monad o] [Assertion Pred] [Assertion EPred] [WPMonad o Pred EPred]
    [IteratorLoop α m n] [IteratorLoop α m o]
    [LawfulIteratorLoop α m n] [LawfulIteratorLoop α m o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    {f : β → n (ULift Bool)} {g : δ → β → o δ} {init : δ} {it : IterM (α := α) m β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h :
        haveI : MonadLift n o := ⟨MonadLiftT.monadLift⟩
        Triple (it.foldM (n := o) (init := init) (fun d b => do if (← f b).down then g d b else Pure.pure d)) P Q eQ) :
    Triple ((it.filterM f).foldM (init := init) g) P Q eQ := by
  rwa [Std.IterM.foldM_filterM]


@[spec]
theorem Spec.IterM.foldM_filterMap {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''}
    {Pred : Type uₚ} {EPred : Type uₑ}
    [Iterator α m β] [Finite α m] [Monad m] [Monad n] [LawfulMonad m] [Assertion Pred] [Assertion EPred] [WPMonad n Pred EPred]
    [IteratorLoop α m n]
    [LawfulIteratorLoop α m n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    {f : β → Option γ} {g : δ → γ → n δ} {init : δ} {it : IterM (α := α) m β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h : Triple (it.foldM (n := n) (init := init) (fun d b => do
          let some c := f b | Pure.pure d
          g d c)) P Q eQ) :
    Triple ((it.filterMap f).foldM (init := init) g) P Q eQ := by
  rwa [Std.IterM.foldM_filterMap]


@[spec]
theorem Spec.IterM.foldM_map {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''}
    {Pred : Type uₚ} {EPred : Type uₑ}
    [Iterator α m β] [Finite α m] [Monad m] [Monad n] [LawfulMonad m] [Assertion Pred] [Assertion EPred] [WPMonad n Pred EPred]
    [IteratorLoop α m n] [LawfulIteratorLoop α m n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    {f : β → γ} {g : δ → γ → n δ} {init : δ} {it : IterM (α := α) m β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h : Triple (it.foldM (init := init) (fun d b => do g d (f b))) P Q eQ) :
    Triple ((it.map f).foldM (init := init) g) P Q eQ := by
  rwa [Std.IterM.foldM_map]


@[spec]
theorem Spec.IterM.foldM_filter {α β δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''}
    {Pred : Type uₚ} {EPred : Type uₑ}
    [Iterator α m β] [Finite α m] [Monad m] [Monad n] [LawfulMonad m] [Assertion Pred] [Assertion EPred] [WPMonad n Pred EPred]
    [IteratorLoop α m n]
    [LawfulIteratorLoop α m n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    {f : β → Bool} {g : δ → β → n δ} {init : δ} {it : IterM (α := α) m β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h : Triple (it.foldM (init := init) (fun d b => if f b then g d b else Pure.pure d)) P Q eQ) :
    Triple ((it.filter f).foldM (init := init) g) P Q eQ := by
  rwa [Std.IterM.foldM_filter]


@[spec]
theorem Spec.IterM.fold_filterMapWithPostcondition {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''}
    {Pred : Type uₚ} {EPred : Type uₑ}
    [Iterator α m β] [Finite α m]
    [Monad m] [LawfulMonad m]
    [Monad n] [Assertion Pred] [Assertion EPred] [WPMonad n Pred EPred]
    [IteratorLoop α m n] [LawfulIteratorLoop α m n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    {f : β → PostconditionT n (Option γ)} {g : δ → γ → δ} {init : δ} {it : IterM (α := α) m β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h : Triple (it.foldM (n := n) (init := init) (fun d b => do
          let some c ← (f b).run | Pure.pure d
          return g d c)) P Q eQ) :
    Triple ((it.filterMapWithPostcondition f).fold (init := init) g) P Q eQ := by
  rwa [Std.IterM.fold_filterMapWithPostcondition]


@[spec]
theorem Spec.IterM.fold_filterMapM {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''}
    {Pred : Type uₚ} {EPred : Type uₑ}
    [Iterator α m β] [Finite α m]
    [Monad m] [LawfulMonad m]
    [Monad n] [MonadAttach n] [WeaklyLawfulMonadAttach n] [Assertion Pred] [Assertion EPred] [WPMonad n Pred EPred]
    [IteratorLoop α m n] [LawfulIteratorLoop α m n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    {f : β → n (Option γ)} {g : δ → γ → δ} {init : δ} {it : IterM (α := α) m β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h : Triple (it.foldM (init := init) (fun d b => do
          let some c ← f b | Pure.pure d
          return g d c)) P Q eQ) :
    Triple ((it.filterMapM f).fold (init := init) g) P Q eQ := by
  rwa [Std.IterM.fold_filterMapM]


@[spec]
theorem Spec.IterM.fold_mapWithPostcondition {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''}
    {Pred : Type uₚ} {EPred : Type uₑ}
    [Iterator α m β] [Finite α m]
    [Monad m] [LawfulMonad m]
    [Monad n] [Assertion Pred] [Assertion EPred] [WPMonad n Pred EPred]
    [IteratorLoop α m n] [LawfulIteratorLoop α m n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    {f : β → PostconditionT n γ} {g : δ → γ → δ} {init : δ} {it : IterM (α := α) m β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h : Triple (it.foldM (init := init) (fun d b => do let c ← (f b).run; return g d c)) P Q eQ) :
    Triple ((it.mapWithPostcondition f).fold (init := init) g) P Q eQ := by
  rwa [Std.IterM.fold_mapWithPostcondition]


@[spec]
theorem Spec.IterM.fold_mapM {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''}
    {Pred : Type uₚ} {EPred : Type uₑ}
    [Iterator α m β] [Finite α m]
    [Monad m] [LawfulMonad m]
    [Monad n] [MonadAttach n] [WeaklyLawfulMonadAttach n] [Assertion Pred] [Assertion EPred] [WPMonad n Pred EPred]
    [IteratorLoop α m n] [LawfulIteratorLoop α m n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    {f : β → n γ} {g : δ → γ → δ} {init : δ} {it : IterM (α := α) m β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h : Triple (it.foldM (init := init) (fun d b => do let c ← f b; return g d c)) P Q eQ) :
    Triple ((it.mapM f).fold (init := init) g) P Q eQ := by
  rwa [Std.IterM.fold_mapM]


@[spec]
theorem Spec.IterM.fold_filterWithPostcondition {α β δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''}
    {Pred : Type uₚ} {EPred : Type uₑ}
    [Iterator α m β] [Finite α m]
    [Monad m] [LawfulMonad m]
    [Monad n] [Assertion Pred] [Assertion EPred] [WPMonad n Pred EPred]
    [IteratorLoop α m n] [LawfulIteratorLoop α m n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    {f : β → PostconditionT n (ULift Bool)} {g : δ → β → δ} {init : δ} {it : IterM (α := α) m β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h : Triple (it.foldM (init := init) (fun d b => return if (← (f b).run).down then g d b else d)) P Q eQ) :
    Triple ((it.filterWithPostcondition f).fold (init := init) g) P Q eQ := by
  rwa [Std.IterM.fold_filterWithPostcondition]


@[spec]
theorem Spec.IterM.fold_filterM {α β δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''}
    {Pred : Type uₚ} {EPred : Type uₑ}
    [Iterator α m β] [Finite α m]
    [Monad m] [LawfulMonad m]
    [Monad n] [MonadAttach n] [WeaklyLawfulMonadAttach n] [Assertion Pred] [Assertion EPred] [WPMonad n Pred EPred]
    [IteratorLoop α m n] [LawfulIteratorLoop α m n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    {f : β → n (ULift Bool)} {g : δ → β → δ} {init : δ} {it : IterM (α := α) m β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h : Triple (it.foldM (init := init) (fun d b => return if (← f b).down then g d b else d)) P Q eQ) :
    Triple ((it.filterM f).fold (init := init) g) P Q eQ := by
  rwa [Std.IterM.fold_filterM]


@[spec]
theorem Spec.IterM.fold_filterMap {α β γ δ : Type w}
    {m : Type w → Type w'}
    {Pred : Type uₚ} {EPred : Type uₑ}
    [Iterator α m β] [Finite α m] [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    [IteratorLoop α m m] [LawfulIteratorLoop α m m]
    {f : β → Option γ} {g : δ → γ → δ} {init : δ} {it : IterM (α := α) m β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h : Triple (it.fold (init := init) (fun d b =>
          match f b with
          | some c => g d c
          | _ => d)) P Q eQ) :
    Triple ((it.filterMap f).fold (init := init) g) P Q eQ := by
  rwa [Std.IterM.fold_filterMap]


@[spec]
theorem Spec.IterM.fold_map {α β γ δ : Type w}
    {m : Type w → Type w'}
    {Pred : Type uₚ} {EPred : Type uₑ}
    [Iterator α m β] [Finite α m] [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    [IteratorLoop α m m] [LawfulIteratorLoop α m m]
    {f : β → γ} {g : δ → γ → δ} {init : δ} {it : IterM (α := α) m β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h : Triple (it.fold (init := init) (fun d b => g d (f b))) P Q eQ) :
    Triple ((it.map f).fold (init := init) g) P Q eQ := by
  rwa [Std.IterM.fold_map]


@[spec]
theorem Spec.IterM.fold_filter {α β δ : Type w}
    {m : Type w → Type w'}
    {Pred : Type uₚ} {EPred : Type uₑ}
    [Iterator α m β] [Finite α m] [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    [IteratorLoop α m m] [LawfulIteratorLoop α m m]
    {f : β → Bool} {g : δ → β → δ} {init : δ} {it : IterM (α := α) m β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h : Triple (it.fold (init := init) (fun d b => if f b then g d b else d)) P Q eQ) :
    Triple ((it.filter f).fold (init := init) g) P Q eQ := by
  rwa [Std.IterM.fold_filter]


@[spec]
theorem Spec.Iter.forIn_filterMapWithPostcondition {α β β₂ γ : Type w}
    {n : Type w → Type w'} {o : Type w → Type w''}
    {Pred : Type uₚ} {EPred : Type uₑ}
    [Iterator α Id β]
    [Monad n] [LawfulMonad n] [Monad o] [Assertion Pred] [Assertion EPred] [WPMonad o Pred EPred]
    [MonadLiftT n o] [LawfulMonadLiftT n o] [Finite α Id]
    [IteratorLoop α Id o] [LawfulIteratorLoop α Id o]
    {it : Iter (α := α) β} {f : β → PostconditionT n (Option β₂)} {init : γ}
    {g : β₂ → γ → o (ForInStep γ)} {P : Pred} {Q : γ → Pred} {eQ : EPred}
    (h : Triple (forIn (m := o) it init (fun out acc => do
        match ← (f out).run with
        | some c => g c acc
        | none => return .yield acc)) P Q eQ) :
    Triple (forIn (it.filterMapWithPostcondition f) init g) P Q eQ := by
  rwa [Std.Iter.forIn_filterMapWithPostcondition]


@[spec]
theorem Spec.Iter.forIn_filterMapM {α β β₂ γ : Type w}
    {n : Type w → Type w'} {o : Type w → Type w''}
    {Pred : Type uₚ} {EPred : Type uₑ}
    [Iterator α Id β]
    [Monad n] [LawfulMonad n] [Monad o] [Assertion Pred] [Assertion EPred] [WPMonad o Pred EPred]
    [MonadAttach n] [WeaklyLawfulMonadAttach n]
    [MonadLiftT n o] [LawfulMonadLiftT n o]
    [Finite α Id] [IteratorLoop α Id o] [LawfulIteratorLoop α Id o]
    {it : Iter (α := α) β} {f : β → n (Option β₂)} {init : γ} {g : β₂ → γ → o (ForInStep γ)}
    {P : Pred} {Q : γ → Pred} {eQ : EPred}
    (h : Triple (forIn (m := o) it init (fun out acc => do
        match ← f out with
        | some c => g c acc
        | none => return .yield acc)) P Q eQ) :
    Triple (forIn (it.filterMapM f) init g) P Q eQ := by
  rwa [Std.Iter.forIn_filterMapM]


@[spec]
theorem Spec.Iter.forIn_filterMap {α β β₂ γ : Type w}
    {n : Type w → Type w'}
    {Pred : Type uₚ} {EPred : Type uₑ}
    [Iterator α Id β]
    [Monad n] [Assertion Pred] [Assertion EPred] [WPMonad n Pred EPred] [Finite α Id]
    [IteratorLoop α Id n] [LawfulIteratorLoop α Id n]
    {it : Iter (α := α) β} {f : β → Option β₂} {init : γ} {g : β₂ → γ → n (ForInStep γ)}
    {P : Pred} {Q : γ → Pred} {eQ : EPred}
    (h : Triple (forIn it init (fun out acc => do
        match f out with
        | some c => g c acc
        | none => return .yield acc)) P Q eQ) :
    Triple (forIn (it.filterMap f) init g) P Q eQ := by
  rwa [Std.Iter.forIn_filterMap]


@[spec]
theorem Spec.Iter.forIn_mapWithPostcondition {α β β₂ γ : Type w}
    {n : Type w → Type w'} {o : Type w → Type w''}
    {Pred : Type uₚ} {EPred : Type uₑ}
    [Iterator α Id β]
    [Monad n] [LawfulMonad n] [Monad o] [Assertion Pred] [Assertion EPred] [WPMonad o Pred EPred]
    [MonadLiftT n o] [LawfulMonadLiftT n o] [Finite α Id]
    [IteratorLoop α Id o] [LawfulIteratorLoop α Id o]
    {it : Iter (α := α) β} {f : β → PostconditionT n β₂} {init : γ}
    {g : β₂ → γ → o (ForInStep γ)} {P : Pred} {Q : γ → Pred} {eQ : EPred}
    (h : Triple (forIn (m := o) it init (fun out acc => do g (← (f out).run) acc)) P Q eQ) :
    Triple (forIn (it.mapWithPostcondition f) init g) P Q eQ := by
  rwa [Std.Iter.forIn_mapWithPostcondition]


@[spec]
theorem Spec.Iter.forIn_mapM {α β β₂ γ : Type w}
    {n : Type w → Type w'} {o : Type w → Type w''}
    {Pred : Type uₚ} {EPred : Type uₑ}
    [Iterator α Id β]
    [Monad n] [LawfulMonad n] [Monad o] [Assertion Pred] [Assertion EPred] [WPMonad o Pred EPred]
    [MonadAttach n] [WeaklyLawfulMonadAttach n]
    [MonadLiftT n o] [LawfulMonadLiftT n o]
    [Finite α Id]
    [IteratorLoop α Id o] [LawfulIteratorLoop α Id o]
    {it : Iter (α := α) β} {f : β → n β₂} {init : γ} {g : β₂ → γ → o (ForInStep γ)}
    {P : Pred} {Q : γ → Pred} {eQ : EPred}
    (h : Triple (forIn (m := o) it init (fun out acc => do g (← f out) acc)) P Q eQ) :
    Triple (forIn (it.mapM f) init g) P Q eQ := by
  rwa [Std.Iter.forIn_mapM]


@[spec]
theorem Spec.Iter.forIn_map {α β β₂ γ : Type w}
    {n : Type w → Type w'}
    {Pred : Type uₚ} {EPred : Type uₑ}
    [Iterator α Id β]
    [Monad n] [Assertion Pred] [Assertion EPred] [WPMonad n Pred EPred]
    [Finite α Id] [IteratorLoop α Id n] [LawfulIteratorLoop α Id n]
    {it : Iter (α := α) β} {f : β → β₂} {init : γ} {g : β₂ → γ → n (ForInStep γ)}
    {P : Pred} {Q : γ → Pred} {eQ : EPred}
    (h : Triple (forIn it init (fun out acc => do g (f out) acc)) P Q eQ) :
    Triple (forIn (it.map f) init g) P Q eQ := by
  rwa [Std.Iter.forIn_map]


@[spec]
theorem Spec.Iter.forIn_filterWithPostcondition {α β γ : Type w}
    {n : Type w → Type w'} {o : Type w → Type w''}
    {Pred : Type uₚ} {EPred : Type uₑ}
    [Iterator α Id β]
    [Monad n] [LawfulMonad n] [Monad o] [Assertion Pred] [Assertion EPred] [WPMonad o Pred EPred]
    [MonadLiftT n o] [LawfulMonadLiftT n o]
    [Finite α Id] [IteratorLoop α Id o] [LawfulIteratorLoop α Id o]
    {it : Iter (α := α) β} {f : β → PostconditionT n (ULift Bool)} {init : γ}
    {g : β → γ → o (ForInStep γ)} {P : Pred} {Q : γ → Pred} {eQ : EPred}
    (h : Triple (forIn (m := o) it init (fun out acc => do if (← (f out).run).down then g out acc else return .yield acc)) P Q eQ) :
    Triple (forIn (it.filterWithPostcondition f) init g) P Q eQ := by
  rwa [Std.Iter.forIn_filterWithPostcondition]


@[spec]
theorem Spec.Iter.forIn_filterM {α β γ : Type w}
    {n : Type w → Type w'} {o : Type w → Type w''}
    {Pred : Type uₚ} {EPred : Type uₑ}
    [Iterator α Id β]
    [Monad n] [LawfulMonad n] [Monad o] [Assertion Pred] [Assertion EPred] [WPMonad o Pred EPred]
    [MonadAttach n] [WeaklyLawfulMonadAttach n]
    [MonadLiftT n o] [LawfulMonadLiftT n o] [Finite α Id]
    [IteratorLoop α Id o] [LawfulIteratorLoop α Id o]
    {it : Iter (α := α) β} {f : β → n (ULift Bool)} {init : γ} {g : β → γ → o (ForInStep γ)}
    {P : Pred} {Q : γ → Pred} {eQ : EPred}
    (h : Triple (forIn (m := o) it init (fun out acc => do if (← f out).down then g out acc else return .yield acc)) P Q eQ) :
    Triple (forIn (it.filterM f) init g) P Q eQ := by
  rwa [Std.Iter.forIn_filterM]


@[spec]
theorem Spec.Iter.forIn_filter {α β γ : Type w}
    {n : Type w → Type w'}
    {Pred : Type uₚ} {EPred : Type uₑ}
    [Iterator α Id β]
    [Monad n] [Assertion Pred] [Assertion EPred] [WPMonad n Pred EPred]
    [Finite α Id] [IteratorLoop α Id n] [LawfulIteratorLoop α Id n]
    {it : Iter (α := α) β} {f : β → Bool} {init : γ} {g : β → γ → n (ForInStep γ)}
    {P : Pred} {Q : γ → Pred} {eQ : EPred}
    (h : Triple (forIn it init (fun out acc => do if f out then g out acc else return .yield acc)) P Q eQ) :
    Triple (forIn (it.filter f) init g) P Q eQ := by
  rwa [Std.Iter.forIn_filter]


@[spec]
theorem Spec.Iter.foldM_filterMapWithPostcondition {α β γ δ : Type w}
    {n : Type w → Type w'} {o : Type w → Type w''}
    {Pred : Type uₚ} {EPred : Type uₑ}
    [Iterator α Id β] [Finite α Id]
    [Monad n] [Monad o] [LawfulMonad n] [Assertion Pred] [Assertion EPred] [WPMonad o Pred EPred]
    [IteratorLoop α Id n] [IteratorLoop α Id o]
    [LawfulIteratorLoop α Id n] [LawfulIteratorLoop α Id o]
    [MonadLiftT n o] [LawfulMonadLiftT n o]
    {f : β → PostconditionT n (Option γ)} {g : δ → γ → o δ} {init : δ} {it : Iter (α := α) β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h : Triple (it.foldM (m := o) (init := init) (fun d b => do
          let some c ← (f b).run | Pure.pure d
          g d c)) P Q eQ) :
    Triple ((it.filterMapWithPostcondition f).foldM (init := init) g) P Q eQ := by
  rwa [Std.Iter.foldM_filterMapWithPostcondition]


@[spec]
theorem Spec.Iter.foldM_filterMapM {α β γ δ : Type w}
    {n : Type w → Type w'} {o : Type w → Type w''}
    {Pred : Type uₚ} {EPred : Type uₑ}
    [Iterator α Id β] [Finite α Id]
    [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [Monad o] [Assertion Pred] [Assertion EPred] [WPMonad o Pred EPred]
    [IteratorLoop α Id n] [IteratorLoop α Id o]
    [LawfulIteratorLoop α Id n] [LawfulIteratorLoop α Id o]
    [MonadLiftT n o] [LawfulMonadLiftT n o]
    {f : β → n (Option γ)} {g : δ → γ → o δ} {init : δ} {it : Iter (α := α) β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h : Triple (it.foldM (m := o) (init := init) (fun d b => do
          let some c ← f b | Pure.pure d
          g d c)) P Q eQ) :
    Triple ((it.filterMapM f).foldM (init := init) g) P Q eQ := by
  rwa [Std.Iter.foldM_filterMapM]


@[spec]
theorem Spec.Iter.foldM_mapWithPostcondition {α β γ δ : Type w}
    {m : Type w → Type w'''} {n : Type w → Type w'} {o : Type w → Type w''}
    {Pred : Type uₚ} {EPred : Type uₑ}
    [Iterator α Id β] [Finite α Id]
    [Monad m] [Monad n] [Monad o] [LawfulMonad m] [LawfulMonad n] [Assertion Pred] [Assertion EPred] [WPMonad o Pred EPred]
    [IteratorLoop α Id n] [IteratorLoop α Id o]
    [LawfulIteratorLoop α Id n] [LawfulIteratorLoop α Id o]
    [MonadLiftT n o] [LawfulMonadLiftT n o]
    {f : β → PostconditionT n γ} {g : δ → γ → o δ} {init : δ} {it : Iter (α := α) β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h : Triple (it.foldM (m := o) (init := init) (fun d b => do let c ← (f b).run; g d c)) P Q eQ) :
    Triple ((it.mapWithPostcondition f).foldM (init := init) g) P Q eQ := by
  rwa [Std.Iter.foldM_mapWithPostcondition (m := m)]


@[spec]
theorem Spec.Iter.foldM_mapM {α β γ δ : Type w}
    {n : Type w → Type w'} {o : Type w → Type w''}
    {Pred : Type uₚ} {EPred : Type uₑ}
    [Iterator α Id β] [Finite α Id]
    [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [Monad o] [Assertion Pred] [Assertion EPred] [WPMonad o Pred EPred]
    [IteratorLoop α Id n] [IteratorLoop α Id o]
    [LawfulIteratorLoop α Id n] [LawfulIteratorLoop α Id o]
    [MonadLiftT n o] [LawfulMonadLiftT n o]
    {f : β → n γ} {g : δ → γ → o δ} {init : δ} {it : Iter (α := α) β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h : Triple (it.foldM (m := o) (init := init) (fun d b => do let c ← f b; g d c)) P Q eQ) :
    Triple ((it.mapM f).foldM (init := init) g) P Q eQ := by
  rwa [Std.Iter.foldM_mapM]


@[spec]
theorem Spec.Iter.foldM_filterWithPostcondition {α β δ : Type w}
    {n : Type w → Type w'} {o : Type w → Type w''}
    {Pred : Type uₚ} {EPred : Type uₑ}
    [Iterator α Id β] [Finite α Id]
    [Monad n] [Monad o] [LawfulMonad n] [Assertion Pred] [Assertion EPred] [WPMonad o Pred EPred]
    [IteratorLoop α Id n] [IteratorLoop α Id o]
    [LawfulIteratorLoop α Id n] [LawfulIteratorLoop α Id o]
    [MonadLiftT n o] [LawfulMonadLiftT n o]
    {f : β → PostconditionT n (ULift Bool)} {g : δ → β → o δ} {init : δ} {it : Iter (α := α) β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h : Triple (it.foldM (m := o) (init := init) (fun d b => do if (← (f b).run).down then g d b else Pure.pure d)) P Q eQ) :
    Triple ((it.filterWithPostcondition f).foldM (init := init) g) P Q eQ := by
  rwa [Std.Iter.foldM_filterWithPostcondition]


@[spec]
theorem Spec.Iter.foldM_filterM {α β δ : Type w}
    {n : Type w → Type w'} {o : Type w → Type w''}
    {Pred : Type uₚ} {EPred : Type uₑ}
    [Iterator α Id β] [Finite α Id]
    [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [Monad o] [Assertion Pred] [Assertion EPred] [WPMonad o Pred EPred]
    [IteratorLoop α Id n] [IteratorLoop α Id o]
    [LawfulIteratorLoop α Id n] [LawfulIteratorLoop α Id o]
    [MonadLiftT n o] [LawfulMonadLiftT n o]
    {f : β → n (ULift Bool)} {g : δ → β → o δ} {init : δ} {it : Iter (α := α) β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h : Triple (it.foldM (m := o) (init := init) (fun d b => do if (← f b).down then g d b else Pure.pure d)) P Q eQ) :
    Triple ((it.filterM f).foldM (init := init) g) P Q eQ := by
  rwa [Std.Iter.foldM_filterM]


@[spec]
theorem Spec.Iter.foldM_filterMap {α β γ δ : Type w}
    {n : Type w → Type w'}
    {Pred : Type uₚ} {EPred : Type uₑ}
    [Iterator α Id β] [Finite α Id] [Monad n] [Assertion Pred] [Assertion EPred] [WPMonad n Pred EPred]
    [IteratorLoop α Id n]
    [LawfulIteratorLoop α Id n]
    {f : β → Option γ} {g : δ → γ → n δ} {init : δ} {it : Iter (α := α) β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h : Triple (it.foldM (init := init) (fun d b => do
          let some c := f b | Pure.pure d
          g d c)) P Q eQ) :
    Triple ((it.filterMap f).foldM (init := init) g) P Q eQ := by
  rwa [Std.Iter.foldM_filterMap]


@[spec]
theorem Spec.Iter.foldM_map {α β γ δ : Type w}
    {n : Type w → Type w'}
    {Pred : Type uₚ} {EPred : Type uₑ}
    [Iterator α Id β] [Finite α Id] [Monad n] [Assertion Pred] [Assertion EPred] [WPMonad n Pred EPred]
    [IteratorLoop α Id n] [LawfulIteratorLoop α Id n]
    {f : β → γ} {g : δ → γ → n δ} {init : δ} {it : Iter (α := α) β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h : Triple (it.foldM (init := init) (fun d b => do g d (f b))) P Q eQ) :
    Triple ((it.map f).foldM (init := init) g) P Q eQ := by
  rwa [Std.Iter.foldM_map]


@[spec]
theorem Spec.Iter.foldM_filter {α β δ : Type w}
    {n : Type w → Type w'}
    {Pred : Type uₚ} {EPred : Type uₑ}
    [Iterator α Id β] [Finite α Id] [Monad n] [Assertion Pred] [Assertion EPred] [WPMonad n Pred EPred]
    [IteratorLoop α Id n] [LawfulIteratorLoop α Id n]
    {f : β → Bool} {g : δ → β → n δ} {init : δ} {it : Iter (α := α) β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h : Triple (it.foldM (init := init) (fun d b => if f b then g d b else Pure.pure d)) P Q eQ) :
    Triple ((it.filter f).foldM (init := init) g) P Q eQ := by
  rwa [Std.Iter.foldM_filter]


@[spec]
theorem Spec.Iter.fold_filterMapWithPostcondition {α β γ δ : Type w}
    {n : Type w → Type w'}
    {Pred : Type uₚ} {EPred : Type uₑ}
    [Iterator α Id β] [Finite α Id]
    [Monad n] [Assertion Pred] [Assertion EPred] [WPMonad n Pred EPred]
    [IteratorLoop α Id n] [LawfulIteratorLoop α Id n]
    {f : β → PostconditionT n (Option γ)} {g : δ → γ → δ} {init : δ} {it : Iter (α := α) β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h : Triple (it.foldM (init := init) (fun d b => do
          let some c ← (f b).run | Pure.pure d
          return g d c)) P Q eQ) :
    Triple ((it.filterMapWithPostcondition f).fold (init := init) g) P Q eQ := by
  rwa [Std.Iter.fold_filterMapWithPostcondition]


@[spec]
theorem Spec.Iter.fold_filterMapM {α β γ δ : Type w}
    {n : Type w → Type w'}
    {Pred : Type uₚ} {EPred : Type uₑ}
    [Iterator α Id β] [Finite α Id]
    [Monad n] [MonadAttach n] [WeaklyLawfulMonadAttach n] [Assertion Pred] [Assertion EPred] [WPMonad n Pred EPred]
    [IteratorLoop α Id n] [LawfulIteratorLoop α Id n]
    {f : β → n (Option γ)} {g : δ → γ → δ} {init : δ} {it : Iter (α := α) β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h : Triple (it.foldM (init := init) (fun d b => do
          let some c ← f b | Pure.pure d
          return g d c)) P Q eQ) :
    Triple ((it.filterMapM f).fold (init := init) g) P Q eQ := by
  rwa [Std.Iter.fold_filterMapM]


@[spec]
theorem Spec.Iter.fold_mapWithPostcondition {α β γ δ : Type w}
    {n : Type w → Type w'}
    {Pred : Type uₚ} {EPred : Type uₑ}
    [Iterator α Id β] [Finite α Id]
    [Monad n] [Assertion Pred] [Assertion EPred] [WPMonad n Pred EPred]
    [IteratorLoop α Id n] [LawfulIteratorLoop α Id n]
    {f : β → PostconditionT n γ} {g : δ → γ → δ} {init : δ} {it : Iter (α := α) β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h : Triple (it.foldM (init := init) (fun d b => do let c ← (f b).run; return g d c)) P Q eQ) :
    Triple ((it.mapWithPostcondition f).fold (init := init) g) P Q eQ := by
  rwa [Std.Iter.fold_mapWithPostcondition]


@[spec]
theorem Spec.Iter.fold_mapM {α β γ δ : Type w}
    {n : Type w → Type w'}
    {Pred : Type uₚ} {EPred : Type uₑ}
    [Iterator α Id β] [Finite α Id]
    [Monad n] [MonadAttach n] [WeaklyLawfulMonadAttach n] [Assertion Pred] [Assertion EPred] [WPMonad n Pred EPred]
    [IteratorLoop α Id n] [LawfulIteratorLoop α Id n]
    {f : β → n γ} {g : δ → γ → δ} {init : δ} {it : Iter (α := α) β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h : Triple (it.foldM (init := init) (fun d b => do let c ← f b; return g d c)) P Q eQ) :
    Triple ((it.mapM f).fold (init := init) g) P Q eQ := by
  rwa [Std.Iter.fold_mapM]


@[spec]
theorem Spec.Iter.fold_filterWithPostcondition {α β δ : Type w}
    {n : Type w → Type w'}
    {Pred : Type uₚ} {EPred : Type uₑ}
    [Iterator α Id β] [Finite α Id]
    [Monad n] [Assertion Pred] [Assertion EPred] [WPMonad n Pred EPred]
    [IteratorLoop α Id n] [LawfulIteratorLoop α Id n]
    {f : β → PostconditionT n (ULift Bool)} {g : δ → β → δ} {init : δ} {it : Iter (α := α) β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h : Triple (it.foldM (init := init) (fun d b => return if (← (f b).run).down then g d b else d)) P Q eQ) :
    Triple ((it.filterWithPostcondition f).fold (init := init) g) P Q eQ := by
  rwa [Std.Iter.fold_filterWithPostcondition]


@[spec]
theorem Spec.Iter.fold_filterM {α β δ : Type w}
    {n : Type w → Type w'}
    {Pred : Type uₚ} {EPred : Type uₑ}
    [Iterator α Id β] [Finite α Id]
    [Monad n] [MonadAttach n] [WeaklyLawfulMonadAttach n] [Assertion Pred] [Assertion EPred] [WPMonad n Pred EPred]
    [IteratorLoop α Id n] [LawfulIteratorLoop α Id n]
    {f : β → n (ULift Bool)} {g : δ → β → δ} {init : δ} {it : Iter (α := α) β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h : Triple (it.foldM (init := init) (fun d b => return if (← f b).down then g d b else d)) P Q eQ) :
    Triple ((it.filterM f).fold (init := init) g) P Q eQ := by
  rwa [Std.Iter.fold_filterM]

end Iterators



@[spec]
theorem Spec.foldlM_array
    {xs : Array α} {init : β} {f : β → α → m β}
    (inv : Invariant α β Pred)
    {epost : EPred}
    (step : ∀ pref cur suff (_h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (f b cur)
        (inv pref (cur::suff) b)
        (fun b' => inv (pref ++ [cur]) suff b')
        epost) :
    Triple
      (Array.foldlM f init xs)
      (inv [] xs.toList init)
      (fun b => inv xs.toList [] b)
      epost := by
  cases xs; simp; apply Spec.foldlM_list inv step

/--
The type of loop invariants used by the specifications of `for ... in ...` loops over strings.
A loop invariant is a function mapping the current position and state to a lattice element.
-/
@[spec_invariant_type, simp, grind =]
def StringInvariant (s : String) (β : Type u) (Pred : Type uₚ) :=
  s.Pos → β → Pred

/-- An invariant combinator for `String` loops with early return, for the new `do` elaborator
which uses `Prod` for the state tuple: `onContinue` is the invariant while iterating, `onReturn`
holds once the loop returned early with a value. -/
noncomputable abbrev StringInvariant.withEarlyReturnNewDo {s : String} {β : Type u} {γ : Type u}
    (Pred : Type uₚ) [Assertion Pred]
    (onContinue : s.Pos → β → Pred)
    (onReturn : γ → β → Pred) :
    StringInvariant s (Option γ × β) Pred :=
  fun pos ⟨x, b⟩ =>
        (⌜x = none⌝ ⊓ onContinue pos b)
      ⊔ (iSup fun r => ⌜x = some r ∧ pos = s.endPos⌝ ⊓ onReturn r b)

@[spec]
theorem Spec.forIn_string
    {s : String} {init : β} {f : Char → β → m (ForInStep β)}
    (inv : StringInvariant s β Pred)
    {epost : EPred}
    (step : ∀ pos b (h : pos ≠ s.endPos),
      Triple
        (f (pos.get h) b)
        (inv pos b)
        (fun r => match r with
          | .yield b' => inv (pos.next h) b'
          | .done b' => inv s.endPos b')
        epost) :
    Triple (forIn s init f) (inv s.startPos init) (fun b => inv s.endPos b) epost := by
  suffices h : ∀ (p : s.Pos) (t₁ t₂ : String) (h : p.Splits t₁ t₂),
      Triple (forIn t₂.toList init f) (inv p init) (fun b => inv s.endPos b) epost by
    simpa using h s.startPos _ _ s.splits_startPos
  intro p
  induction p using String.Pos.next_induction generalizing init with
  | next p hp ih =>
    intro t₁ t₂ hsp
    obtain ⟨t₂, rfl⟩ := hsp.exists_eq_singleton_append hp
    simp only [String.toList_append, String.toList_singleton, List.cons_append, List.nil_append,
      List.forIn_cons]
    apply Triple.bind
    case hx => exact step _ _ hp
    case hf =>
      intro r
      cases r with
      | yield b => exact ih _ _ hsp.next
      | done b => exact Triple.pure _ (by dsimp; exact Lean.Order.PartialOrder.rel_refl)
  | endPos =>
    intro t₁ t₂ hsp
    obtain ⟨-, rfl⟩ := String.splits_endPos_iff.mp hsp
    simp only [String.toList_empty, List.forIn_nil]
    exact Triple.pure init Lean.Order.PartialOrder.rel_refl

/--
The type of loop invariants used by the specifications of `for ... in ...` loops over string slices.
A loop invariant is a function mapping the current position and state to a lattice element.
-/
@[spec_invariant_type, simp, grind =]
def StringSliceInvariant (s : String.Slice) (β : Type u) (Pred : Type uₚ) :=
  s.Pos → β → Pred

/-- An invariant combinator for `String.Slice` loops with early return, for the new `do`
elaborator which uses `Prod` for the state tuple: `onContinue` is the invariant while iterating,
`onReturn` holds once the loop returned early with a value. -/
noncomputable abbrev StringSliceInvariant.withEarlyReturnNewDo {s : String.Slice} {β : Type u}
    {γ : Type u} (Pred : Type uₚ) [Assertion Pred]
    (onContinue : s.Pos → β → Pred)
    (onReturn : γ → β → Pred) :
    StringSliceInvariant s (Option γ × β) Pred :=
  fun pos ⟨x, b⟩ =>
        (⌜x = none⌝ ⊓ onContinue pos b)
      ⊔ (iSup fun r => ⌜x = some r ∧ pos = s.endPos⌝ ⊓ onReturn r b)

@[spec]
theorem Spec.forIn_stringSlice
    {s : String.Slice} {init : β} {f : Char → β → m (ForInStep β)}
    (inv : StringSliceInvariant s β Pred)
    {epost : EPred}
    (step : ∀ pos b (h : pos ≠ s.endPos),
      Triple
        (f (pos.get h) b)
        (inv pos b)
        (fun r => match r with
          | .yield b' => inv (pos.next h) b'
          | .done b' => inv s.endPos b')
        epost) :
    Triple (forIn s init f) (inv s.startPos init) (fun b => inv s.endPos b) epost := by
  suffices h : ∀ (p : s.Pos) (t₁ t₂ : String) (h : p.Splits t₁ t₂),
      Triple (forIn t₂.toList init f) (inv p init) (fun b => inv s.endPos b) epost by
    simpa using h s.startPos _ _ s.splits_startPos
  intro p
  induction p using String.Slice.Pos.next_induction generalizing init with
  | next p hp ih =>
    intro t₁ t₂ hsp
    obtain ⟨t₂, rfl⟩ := hsp.exists_eq_singleton_append hp
    simp only [String.toList_append, String.toList_singleton, List.cons_append, List.nil_append,
      List.forIn_cons]
    apply Triple.bind
    case hx => exact step _ _ hp
    case hf =>
      intro r
      cases r with
      | yield b => exact ih _ _ hsp.next
      | done b => exact Triple.pure _ (by dsimp; exact Lean.Order.PartialOrder.rel_refl)
  | endPos =>
    intro t₁ t₂ hsp
    obtain ⟨-, rfl⟩ := String.Slice.splits_endPos_iff.mp hsp
    simp only [String.toList_empty, List.forIn_nil]
    exact Triple.pure init Lean.Order.PartialOrder.rel_refl

section While

universe uα uγ v' s

variable {α β : Type u} {m : Type u → Type v} {Pred : Type uₚ} {EPred : Type uₑ}
variable [Monad m] [Lean.Order.MonadTail m] [Assertion Pred] [Assertion EPred]
  [WPMonad m Pred EPred]

open Assertion

/--
An invariant for a `repeatM` loop, given as a predicate over the `α ⊕ β` cursor:
`.inl a` is the `continue` case at `a`; `.inr b` is the `break` case with result `b`.
-/
@[spec_invariant_type, simp, grind =]
def RepeatInvariant (α β : Type u) (Pred : Type uₚ) :=
  α ⊕ β → Pred

/--
A termination measure for a `repeatM` loop: a type `γ` of measure values equipped with a
well-founded relation, and a lattice-embedded evaluation of the measure at each cursor.
Build one from a measure function with `RepeatVariant.ofMeasure`.
-/
@[spec_invariant_type]
structure RepeatVariant (α : Type uα) (Pred : Type u) [Assertion Pred] :
    Type (max uα (uγ + 1) u) where
  /-- The type of measure values. -/
  {γ : Type uγ}
  /-- The well-founded relation that measure values decrease along. -/
  [wfRel : WellFoundedRelation γ]
  /-- Relates the measure at cursor `a` to a value `n` inside the assertion lattice. -/
  EvalsTo : α → γ → Pred
  /-- The measure evaluates to some value. -/
  total : ∀ a, (⨆ n, EvalsTo a n) = ⊤

namespace RepeatVariant

variable {α : Type uα}

/-- The relation that measure values decrease along. -/
def rel (v : RepeatVariant α Pred) : v.γ → v.γ → Prop :=
  v.wfRel.rel

theorem wf (v : RepeatVariant α Pred) : WellFounded v.rel :=
  v.wfRel.wf

/-- Eliminate the covering join of `EvalsTo` from the left of an entailment. -/
theorem le_of_total_le (v : RepeatVariant α Pred) (a : α) {P Q : Pred}
    [PreservesSup (meet P)]
    (h : (⨆ n, v.EvalsTo a n ⊓ P) ⊑ Q) : P ⊑ Q := by
  have h1 : P ⊑ (⨆ n, v.EvalsTo a n) ⊓ P := by
    rw [v.total a, CompleteLattice.top_meet]
  have h2 : (⨆ n, v.EvalsTo a n) ⊓ P ⊑ ⨆ n, v.EvalsTo a n ⊓ P :=
    iSup_meet_le fun n => le_iSup (fun n => v.EvalsTo a n ⊓ P) n
  exact PartialOrder.rel_trans h1 (PartialOrder.rel_trans h2 h)

/--
Build a `RepeatVariant` from a measure function `f`. The measure's value type `γ` (its codomain
through any `NondetFun` state layers) provides the well-founded relation, e.g. `<` for `Nat` and
the lexicographic order for products.
-/
@[instance_reducible] def ofMeasure {γ : Type uγ} {Fun : Type v'} [NondetFun Pred Fun γ]
    [WellFoundedRelation γ] (f : α → Fun) : RepeatVariant α Pred where
  γ := γ
  EvalsTo a n := NondetFun.EvalsTo (f a) n
  total a := NondetFun.total (f a)

@[simp, grind =] theorem γ_ofMeasure {γ : Type uγ} {Fun : Type v'} [NondetFun Pred Fun γ]
    [WellFoundedRelation γ] (f : α → Fun) :
    (ofMeasure (Pred := Pred) f).γ = γ := rfl

@[simp, grind =] theorem evalsTo_ofMeasure {γ : Type uγ} {Fun : Type v'} [NondetFun Pred Fun γ]
    [WellFoundedRelation γ] (f : α → Fun) (a : α) (n : γ) :
    (ofMeasure (Pred := Pred) f).EvalsTo a n = NondetFun.EvalsTo (f a) n := rfl

/-- Decrease along `ofMeasure` is decrease of measure values along the well-founded relation of
`γ`. Rewriting with this lemma brings a decrease proof obligation into the shape produced by
`termination_by`, so that `decreasing_tactic` applies. -/
theorem rel_ofMeasure {γ : Type uγ} {Fun : Type v'} [NondetFun Pred Fun γ]
    [WellFoundedRelation γ] (f : α → Fun) (n' n : γ) :
    (ofMeasure (Pred := Pred) f).rel n' n ↔ WellFoundedRelation.rel n' n := Iff.rfl

@[simp, grind =] theorem rel_ofMeasure_nat {α : Type} {Pred : Type} [Assertion Pred]
    {Fun : Type} [NondetFun Pred Fun Nat] (f : α → Fun) (n' n : Nat) :
    (ofMeasure (Pred := Pred) f).rel n' n ↔ n' < n := Iff.rfl

/-- The measure at cursor `a'` evaluates to a value strictly below `ma`. -/
noncomputable def EvalsBelow (v : RepeatVariant α Pred) (a' : α) (ma : v.γ) : Pred :=
  ⨆ ma', v.EvalsTo a' ma' ⊓ ⌜v.rel ma' ma⌝

open Std.Internal.Do.CompleteLattice in
/-- For a state-independent measure the pinned value is the measure itself, so the join
collapses to a decrease along the well-founded relation of `γ`. The proof obligation has the
shape produced by `termination_by`, so that `decreasing_tactic` applies. -/
theorem evalsBelow_ofMeasure {γ : Type uγ} [WellFoundedRelation γ]
    (f : α → γ) (a' : α) (ma : γ) :
    (ofMeasure (Pred := Pred) f).EvalsBelow a' ma = ⌜WellFoundedRelation.rel (f a') ma⌝ := by
  refine PartialOrder.rel_antisymm (iSup_le _ _ fun ma' => ?_) (le_iSup_of_le (f a') ?_)
  · refine ofProp_meet_le_left fun h => ?_
    subst h
    exact PartialOrder.rel_refl
  · refine le_meet _ _ _ ?_ PartialOrder.rel_refl
    simp only [evalsTo_ofMeasure, NondetFun.evalsTo_pure]
    rw [ofProp_eq_top trivial]
    exact le_top _

open Std.Internal.Do.CompleteLattice in
@[simp, grind =] theorem evalsBelow_ofMeasure_nat {α : Type} {Pred : Type} [Assertion Pred]
    (f : α → Nat) (a' : α) (ma : Nat) :
    (ofMeasure (Pred := Pred) f).EvalsBelow a' ma = ⌜f a' < ma⌝ :=
  evalsBelow_ofMeasure f a' ma

/-- Pointwise characterization of `EvalsBelow` on a function lattice, for `ofMeasure`
measures. -/
@[simp] theorem evalsBelow_ofMeasure_apply {σ : Type s} {Pred : Type u} [Assertion Pred]
    {γ : Type uγ} {Fun : Type v'} [NondetFun Pred Fun γ] [WellFoundedRelation γ]
    (f : α → σ → Fun) (a' : α) (ma : γ) (s : σ) :
    (ofMeasure (Pred := σ → Pred) f).EvalsBelow a' ma s
      = (ofMeasure (Pred := Pred) (f · s)).EvalsBelow a' ma := by
  simp only [EvalsBelow, iSup_apply, meet_apply, CompleteLattice.ofProp_apply]
  rfl

/-! Fixed-arity specializations of `evalsBelow_ofMeasure_apply` for `Nat`-valued measures at a
lattice tower ending in `Prop`, in the manner of `CompleteLattice.ofProp_apply_1` and its
siblings: the ground instances leave every parameter recoverable from the trigger, so these are
usable `@[grind =]` lemmas where the general `evalsBelow_ofMeasure_apply` is not. -/

@[grind =] theorem evalsBelow_ofMeasure_apply_1 {α : Type} {σ₁ : Type}
    (f : α → σ₁ → Nat) (a' : α) (ma : Nat) (s₁ : σ₁) :
    (ofMeasure (Pred := σ₁ → Prop) f).EvalsBelow a' ma s₁ = (f a' s₁ < ma) := by
  simp

@[grind =] theorem evalsBelow_ofMeasure_apply_2 {α : Type} {σ₁ σ₂ : Type}
    (f : α → σ₁ → σ₂ → Nat) (a' : α) (ma : Nat) (s₁ : σ₁) (s₂ : σ₂) :
    (ofMeasure (Pred := σ₁ → σ₂ → Prop) f).EvalsBelow a' ma s₁ s₂ = (f a' s₁ s₂ < ma) := by
  simp

@[grind =] theorem evalsBelow_ofMeasure_apply_3 {α : Type} {σ₁ σ₂ σ₃ : Type}
    (f : α → σ₁ → σ₂ → σ₃ → Nat) (a' : α) (ma : Nat) (s₁ : σ₁) (s₂ : σ₂) (s₃ : σ₃) :
    (ofMeasure (Pred := σ₁ → σ₂ → σ₃ → Prop) f).EvalsBelow a' ma s₁ s₂ s₃
      = (f a' s₁ s₂ s₃ < ma) := by
  simp

@[grind =] theorem evalsBelow_ofMeasure_apply_4 {α : Type} {σ₁ σ₂ σ₃ σ₄ : Type}
    (f : α → σ₁ → σ₂ → σ₃ → σ₄ → Nat) (a' : α) (ma : Nat) (s₁ : σ₁) (s₂ : σ₂) (s₃ : σ₃)
    (s₄ : σ₄) :
    (ofMeasure (Pred := σ₁ → σ₂ → σ₃ → σ₄ → Prop) f).EvalsBelow a' ma s₁ s₂ s₃ s₄
      = (f a' s₁ s₂ s₃ s₄ < ma) := by
  simp

@[grind =] theorem evalsBelow_ofMeasure_apply_5 {α : Type} {σ₁ σ₂ σ₃ σ₄ σ₅ : Type}
    (f : α → σ₁ → σ₂ → σ₃ → σ₄ → σ₅ → Nat) (a' : α) (ma : Nat) (s₁ : σ₁) (s₂ : σ₂)
    (s₃ : σ₃) (s₄ : σ₄) (s₅ : σ₅) :
    (ofMeasure (Pred := σ₁ → σ₂ → σ₃ → σ₄ → σ₅ → Prop) f).EvalsBelow a' ma s₁ s₂ s₃ s₄ s₅
      = (f a' s₁ s₂ s₃ s₄ s₅ < ma) := by
  simp

end RepeatVariant

open Std.Internal.Do.CompleteLattice in
/--
Specification for `repeatM`. The user supplies a termination `measure`, an invariant, and a step
`Triple` whose pre asserts the measure evaluates to `ma` and the in-progress invariant holds, and
whose post either continues with a measure value below `ma` (the invariant still holding) or
finishes with the `.inr` invariant.
-/
@[spec]
theorem Spec.repeatM
    {init : α} {f : α → m (α ⊕ β)} [Nonempty β] [∀ P : Pred, PreservesSup (meet P)]
    (measure : RepeatVariant α Pred)
    (inv : RepeatInvariant α β Pred)
    (einv : EPred)
    (step : ∀ a (ma : measure.γ),
      Triple
        (f a)
        (measure.EvalsTo a ma ⊓ inv (.inl a))
        (fun r => match r with
          | .inl a' => measure.EvalsBelow a' ma ⊓ inv (.inl a')
          | .inr b => inv (.inr b))
        einv) :
    Triple
      (repeatM f init)
      (inv (.inl init))
      (fun b => inv (.inr b))
      einv := by
  refine Triple.intro <| measure.le_of_total_le init ?_
  refine iSup_le _ _ fun minit => ?_
  suffices key : ∀ (n : measure.γ), Acc measure.rel n → ∀ (a : α),
      Triple
        (_root_.repeatM f a)
        (measure.EvalsTo a n ⊓ inv (.inl a))
        (fun b => inv (.inr b))
        einv
    from (key minit (measure.wf.apply minit) init).le_wp
  intro n hacc
  induction hacc with
  | intro n _ ih =>
    intro a
    rw [_root_.repeatM.Internal.eq_of_monadTail (f := f) a]
    refine Triple.bind (f := fun x => match x with
      | .inl a' => _root_.repeatM f a'
      | .inr b => Pure.pure b)
      (f a) (fun r => match r with
        | .inl a' => measure.EvalsBelow a' n ⊓ inv (.inl a')
        | .inr b => inv (.inr b))
      (step a n) ?_
    rintro (a' | b)
    · refine Triple.intro ?_
      refine iSup_meet_le fun ma' => ?_
      rw [meet_comm (P := measure.EvalsTo a' ma'), meet_assoc]
      exact ofProp_meet_le_left fun hlt => (ih ma' hlt a').le_wp
    · exact Triple.pure b Lean.Order.PartialOrder.rel_refl

/--
Construct an invariant from a loop invariant `inv` and a break condition `onBreak`.

`inv` holds at the end of every loop iteration (including the breaking one), and `onBreak` holds in
addition to `inv` once the loop is done. For a normal `while` loop `onBreak` can be taken as the
negation of the loop condition.
-/
@[simp]
noncomputable abbrev RepeatInvariant.ofInvariantAndBreak {α : Type u} {Pred : Type u} [Assertion Pred]
    (inv : α → Pred) (onBreak : α → Pred) : RepeatInvariant α α Pred
  | .inl a => inv a
  | .inr a => inv a ⊓ onBreak a


/--
Specification for `forIn` over a `Lean.Loop`. The cursor is `β ⊕ β`: `.inl b` means
"still iterating with `b`", `.inr b` means "finished with result `b`".
-/
@[spec]
theorem Spec.forIn_loop
    {l : Lean.Loop} {init : β} {f : Unit → β → m (ForInStep β)}
    [∀ P : Pred, PreservesSup (meet P)]
    (measure : RepeatVariant β Pred)
    (inv : RepeatInvariant β β Pred)
    (einv : EPred)
    (step : ∀ b (mb : measure.γ),
      Triple
        (f () b)
        (measure.EvalsTo b mb ⊓ inv (.inl b))
        (fun r => match r with
          | .yield b' => measure.EvalsBelow b' mb ⊓ inv (.inl b')
          | .done b' => inv (.inr b'))
        einv) :
    Triple
      (forIn l init f)
      (inv (.inl init))
      (fun b => inv (.inr b))
      einv := by
  haveI : Nonempty β := ⟨init⟩
  change Triple (pre := inv (.inl init)) (_root_.Lean.Loop.forIn l init f)
    (fun b => inv (.inr b)) einv
  simp only [_root_.Lean.Loop.forIn]
  apply Spec.repeatM (measure := measure) (inv := inv) (einv := einv)
  intro b mb
  apply Triple.bind
  · exact step b mb
  · intro r
    cases r with
    | yield b' => exact Triple.pure (Sum.inl b') Lean.Order.PartialOrder.rel_refl
    | done b' => exact Triple.pure (Sum.inr b') Lean.Order.PartialOrder.rel_refl

end While

end Std.Internal.Do
