/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Std.Do.WP.Basic
public import Std.Do.WP.Monad

@[expose] public section

/-!
# Simp lemmas for working with weakest preconditions

Many weakest preconditions are so simple that we can compute them directly or
express them in terms of "simpler" weakest preconditions.
This module provides simp lemmas targeting expressions of the form `wp⟦x⟧ Q`
and rewrites them to expressions of simpler weakest preconditions.
-/

namespace Std.Do.WP

open WPMonad

universe u v
variable {m : Type u → Type v} {ps : PostShape.{u}}

/-! ## `WP` -/

@[simp]
theorem ReaderT_run [WP m ps] (x : ReaderT ρ m α) :
  wp⟦x.run r⟧ Q = wp⟦x⟧ (fun a _ => Q.1 a, Q.2) r := rfl

@[simp]
theorem StateT_run [WP m ps] (x : StateT σ m α) :
  wp⟦x.run s⟧ Q = wp⟦x⟧ (fun a s => Q.1 (a, s), Q.2) s := rfl

@[simp]
theorem ExceptT_run [WP m ps] (x : ExceptT ε m α) :
    wp⟦x.run⟧ Q = wp⟦x⟧ (fun a => Q.1 (.ok a), fun e => Q.1 (.error e), Q.2) := by
  simp [wp, ExceptT.run]
  congr
  (ext x; cases x) <;> rfl

/-! ## `WPMonad` -/

@[simp]
theorem pure [Monad m] [WPMonad m ps] (a : α) (Q : PostCond α ps) :
  wp⟦pure (f:=m) a⟧ Q = Q.1 a := by simp [WPMonad.wp_pure]

@[simp]
theorem bind [Monad m] [WPMonad m ps] (x : m α) (f : α → m β) (Q : PostCond β ps) :
  wp⟦x >>= f⟧ Q = wp⟦x⟧ (fun a => wp⟦f a⟧ Q, Q.2) := by simp [WPMonad.wp_bind]

@[simp]
theorem map [Monad m] [WPMonad m ps] (f : α → β) (x : m α) (Q : PostCond β ps) :
  wp⟦f <$> x⟧ Q = wp⟦x⟧ (fun a => Q.1 (f a), Q.2) := by simp [WPMonad.wp_map]

@[simp]
theorem seq [Monad m] [WPMonad m ps] (f : m (α → β)) (x : m α) (Q : PostCond β ps) :
  wp⟦f <*> x⟧ Q = wp⟦f⟧ (fun f => wp⟦x⟧ (fun a => Q.1 (f a), Q.2), Q.2) := by simp [WPMonad.wp_seq]

/-! ## `MonadLift`

The definitions that follow interpret `liftM` and thus instances of, e.g., `MonadStateOf`.

-/

section MonadLift

@[simp]
theorem monadLift_StateT [Monad m] [WPMonad m ps] (x : m α) (Q : PostCond α (.arg σ ps)) :
  wp⟦MonadLift.monadLift x : StateT σ m α⟧ Q = fun s => wp⟦x⟧ (fun a => Q.1 a s, Q.2) := by simp [wp, MonadLift.monadLift, StateT.lift]

@[simp]
theorem monadLift_ReaderT [Monad m] [WPMonad m ps] (x : m α) (Q : PostCond α (.arg ρ ps)) :
  wp⟦MonadLift.monadLift x : ReaderT ρ m α⟧ Q = fun s => wp⟦x⟧ (fun a => Q.1 a s, Q.2) := rfl

@[simp]
theorem monadLift_ExceptT [Monad m] [WPMonad m ps] (x : m α) (Q : PostCond α (.except ε ps)) :
  wp⟦MonadLift.monadLift x : ExceptT ε m α⟧ Q = wp⟦x⟧ (fun a => Q.1 a, Q.2.2) := by
    simp [wp, MonadLift.monadLift, ExceptT.lift, ExceptT.mk]

@[simp]
theorem monadLift_trans [WP o ps] [MonadLift n o] [MonadLiftT m n] :
  wp⟦MonadLiftT.monadLift x : o α⟧ Q = wp⟦MonadLift.monadLift (m:=n) (MonadLiftT.monadLift (m:=m) x) : o α⟧ Q := rfl

@[simp]
theorem monadLift_refl [WP m ps] :
  wp⟦MonadLiftT.monadLift x : m α⟧ Q = wp⟦x : m α⟧ Q := rfl

-- instances

@[simp]
theorem lift_StateT [WP m ps] [Monad m] (x : m α) :
  wp⟦StateT.lift x : StateT σ m α⟧ Q = wp⟦MonadLift.monadLift x : StateT σ m α⟧ Q := rfl

@[simp]
theorem lift_ExceptT [WP m ps] [Monad m] (x : m α) :
  wp⟦ExceptT.lift x : ExceptT ε m α⟧ Q = wp⟦MonadLift.monadLift x : ExceptT ε m α⟧ Q := rfl


-- MonadReader

@[simp]
theorem read_MonadReaderOf [MonadReaderOf ρ m] [MonadLift m n] [WP n _] :
  wp⟦MonadReaderOf.read : n ρ⟧ Q = wp⟦MonadLift.monadLift (MonadReader.read : m ρ) : n ρ⟧ Q := rfl

@[simp]
theorem readThe [MonadReaderOf ρ m] [WP m ps] :
  wp⟦readThe ρ : m ρ⟧ Q = wp⟦MonadReaderOf.read : m ρ⟧ Q := rfl

@[simp]
theorem read_MonadReader [MonadReaderOf ρ m] [WP m ps] :
  wp⟦MonadReader.read : m ρ⟧ Q = wp⟦MonadReaderOf.read : m ρ⟧ Q := rfl

-- MonadState

@[simp]
theorem get_MonadStateOf [MonadStateOf σ m] [MonadLift m n] [WP n _] :
  wp⟦MonadStateOf.get : n σ⟧ Q = wp⟦MonadLift.monadLift (MonadStateOf.get : m σ) : n σ⟧ Q := rfl

@[simp]
theorem get_MonadState [WP m ps] [MonadStateOf σ m] :
  wp⟦MonadState.get : m σ⟧ Q = wp⟦MonadStateOf.get : m σ⟧ Q := rfl

@[simp]
theorem getThe_MonadStateOf [WP m ps] [MonadStateOf σ m] :
  wp⟦getThe σ : m σ⟧ Q = wp⟦MonadStateOf.get : m σ⟧ Q := rfl

@[simp]
theorem set_MonadStateOf [MonadStateOf σ m] [MonadLift m n] [WP n _] :
  wp⟦MonadStateOf.set x : n PUnit⟧ Q = wp⟦MonadLift.monadLift (MonadStateOf.set (σ:=σ) x : m PUnit) : n PUnit⟧ Q := rfl

@[simp]
theorem set_MonadState [WP m ps] [MonadStateOf σ m] :
  wp⟦MonadState.set x : m PUnit⟧ Q = wp⟦MonadStateOf.set x : m PUnit⟧ Q := rfl

@[simp]
theorem modifyGet_MonadStateOf [MonadStateOf σ m] [MonadLift m n] [WP n _]
  (f : σ → α × σ) :
  wp⟦MonadStateOf.modifyGet f : n α⟧ Q = wp⟦MonadLift.monadLift (MonadState.modifyGet f : m α) : n α⟧ Q := rfl

@[simp]
theorem modifyGet_MonadState [WP m ps] [MonadStateOf σ m] (f : σ → α × σ) :
  wp⟦MonadState.modifyGet f : m α⟧ Q = wp⟦MonadStateOf.modifyGet f : m α⟧ Q := rfl

@[simp]
theorem modifyGetThe_MonadStateOf [WP m ps] [MonadStateOf σ m] (f : σ → α × σ) :
  wp⟦modifyGetThe σ f : m α⟧ Q = wp⟦MonadStateOf.modifyGet f : m α⟧ Q := rfl

@[simp]
theorem modify_MonadStateOf [WP m ps] [MonadStateOf σ m] (f : σ → σ) :
  wp⟦modify f : m PUnit⟧ Q = wp⟦MonadStateOf.modifyGet fun s => (⟨⟩, f s) : m PUnit⟧ Q := rfl

@[simp]
theorem modifyThe_MonadStateOf [WP m ps] [MonadStateOf σ m] (f : σ → σ) :
  wp⟦modifyThe σ f : m PUnit⟧ Q = wp⟦MonadStateOf.modifyGet fun s => (⟨⟩, f s) : m PUnit⟧ Q := rfl

-- instances

@[simp]
theorem read_ReaderT [Monad m] [WPMonad m ps] :
    wp⟦MonadReaderOf.read : ReaderT ρ m ρ⟧ Q = fun r => Q.1 r r := by
  simp [wp, MonadReaderOf.read, ReaderT.read]

@[simp]
theorem get_StateT [Monad m] [WPMonad m ps] :
    wp⟦MonadStateOf.get : StateT σ m σ⟧ Q = fun s => Q.1 s s := by
  simp [wp, MonadStateOf.get, StateT.get]

@[simp]
theorem set_StateT [Monad m] [WPMonad m ps] (x : σ) :
    wp⟦MonadStateOf.set x : StateT σ m PUnit⟧ Q = fun _ => Q.1 ⟨⟩ x := by
  simp [wp, set, StateT.set]

@[simp]
theorem modifyGet_StateT [Monad m] [WPMonad m ps] (f : σ → α × σ) :
    wp⟦MonadStateOf.modifyGet f : StateT σ m α⟧ Q = fun s => Q.1 (f s).1 (f s).2 := by
  simp [wp, MonadStateOf.modifyGet, StateT.modifyGet]

@[simp]
theorem get_EStateM :
    wp⟦MonadStateOf.get : EStateM ε σ σ⟧ Q = fun s => Q.1 s s := by
  simp [wp, MonadStateOf.get, EStateM.get]

@[simp]
theorem set_EStateM (x : σ) :
    wp⟦MonadStateOf.set x : EStateM ε σ PUnit⟧ Q = fun _ => Q.1 ⟨⟩ x := by
  simp [wp, set, EStateM.set]

@[simp]
theorem modifyGet_EStateM (f : σ → α × σ) :
    wp⟦MonadStateOf.modifyGet f : EStateM ε σ α⟧ Q = fun s => Q.1 (f s).1 (f s).2 := by
  simp [wp, MonadStateOf.modifyGet, EStateM.modifyGet]

end MonadLift

/-! ## `MonadFunctor`

The definitions that follow interpret `monadMap` and thus instances of, e.g., `MonadReaderWithOf`.

-/

section MonadFunctor

open MonadFunctor renaming monadMap → mmap

-- The following 3 theorems are analogous to *.monadLift_apply.
-- In the past, we experimented with a more tricky definition by rewriting to special monadMap defns on PredTrans, involving
--   wp1 : (∀ {α}, m α → m α) → PredTrans ps α → PredTrans ps α
-- that enjoys quite a tricky definition.
-- However, we found that relying on specialised lemmas is both much simpler and more reliable.
@[simp]
theorem monadMap_StateT [Monad m] [WP m ps]
  (f : ∀{β}, m β → m β) {α} (x : StateT σ m α) (Q : PostCond α (.arg σ ps)) :
    wp⟦mmap (m:=m) f x⟧ Q = fun s => wp⟦f (x.run s)⟧ (fun (a, s) => Q.1 a s, Q.2) := by
  simp [wp, MonadFunctor.monadMap, StateT.run]

@[simp]
theorem monadMap_ReaderT [Monad m] [WP m ps]
  (f : ∀{β}, m β → m β) {α} (x : ReaderT ρ m α) (Q : PostCond α (.arg ρ ps)) :
    wp⟦mmap (m:=m) f x⟧ Q = fun s => wp⟦f (x.run s)⟧ (fun a => Q.1 a s, Q.2) := by
  simp [wp, MonadFunctor.monadMap, ReaderT.run]

@[simp]
theorem monadMap_ExceptT [Monad m] [WP m ps]
  (f : ∀{β}, m β → m β) {α} (x : ExceptT ε m α) (Q : PostCond α (.except ε ps)) :
    wp⟦mmap (m:=m) f x⟧ Q = wp⟦f x.run⟧ (fun | .ok a => Q.1 a | .error e => Q.2.1 e, Q.2.2) := by
  simp [wp, MonadFunctor.monadMap, ExceptT.run]
  congr; ext; split <;> rfl

@[simp]
theorem monadMap_trans [WP o ps] [MonadFunctor n o] [MonadFunctorT m n] :
  wp⟦MonadFunctorT.monadMap f x : o α⟧ Q = wp⟦MonadFunctor.monadMap (m:=n) (MonadFunctorT.monadMap (m:=m) f) x : o α⟧ Q := rfl

@[simp]
theorem monadMap_refl [WP m ps] :
  wp⟦MonadFunctorT.monadMap f x : m α⟧ Q = wp⟦f x : m α⟧ Q := rfl

@[simp]
theorem withReader_ReaderT [WP m ps] :
  wp⟦MonadWithReaderOf.withReader f x : ReaderT ρ m α⟧ Q = fun r => wp⟦x⟧ (fun a _ => Q.1 a r, Q.2) (f r) := rfl

@[simp]
theorem withReader_MonadWithReaderOf [MonadWithReaderOf ρ m] [WP n nsh] [MonadFunctor m n] (f : ρ → ρ) (x : n α) :
  wp⟦MonadWithReaderOf.withReader f x⟧ Q = wp⟦mmap (m:=m) (MonadWithReaderOf.withReader f) x⟧ Q := rfl

@[simp]
theorem withReader_MonadWithReader [MonadWithReaderOf ρ m] [WP m ps] (f : ρ → ρ) (x : m α) :
  wp⟦MonadWithReader.withReader f x⟧ Q = wp⟦MonadWithReaderOf.withReader f x⟧ Q := rfl

@[simp]
theorem withTheReader [MonadWithReaderOf ρ m] [WP m ps] (f : ρ → ρ) (x : m α) :
  wp⟦withTheReader ρ f x⟧ Q = wp⟦MonadWithReaderOf.withReader f x⟧ Q := rfl

end MonadFunctor

/-! ## `MonadExceptOf`

The definitions that follow interpret `throw`, `throwThe`, `tryCatch`, etc.

Since `MonadExceptOf` cannot be lifted through `MonadLift` or `MonadFunctor`, there is one lemma per
`MonadExceptOf` operation and instance to lift through; the classic m*n instances problem.

-/

section MonadExceptOf

@[simp]
theorem throw_MonadExcept [MonadExceptOf ε m] [WP m ps] :
  wp⟦throw e : m α⟧ Q = wp⟦MonadExceptOf.throw e : m α⟧ Q := rfl

@[simp]
theorem throwThe [MonadExceptOf ε m] [WP m ps] :
  wp⟦throwThe ε e : m α⟧ Q = wp⟦MonadExceptOf.throw e : m α⟧ Q := rfl

@[simp]
theorem throw_Except :
    wp⟦MonadExceptOf.throw e : Except ε α⟧ Q = Q.2.1 e := by
  simp [wp, MonadExceptOf.throw, Id.run]

@[simp]
theorem throw_ExceptT [Monad m] [WPMonad m ps] :
    wp⟦MonadExceptOf.throw e : ExceptT ε m α⟧ Q = Q.2.1 e := by
  simp [wp, MonadExceptOf.throw, ExceptT.mk]

@[simp]
theorem throw_EStateM :
    wp⟦MonadExceptOf.throw e : EStateM ε σ α⟧ Q = Q.2.1 e := by
  simp [wp, MonadExceptOf.throw, EStateM.throw]

@[simp]
theorem throw_ReaderT [WP m sh] [Monad m] [MonadExceptOf ε m] :
  wp⟦MonadExceptOf.throw (ε:=ε) e : ReaderT ρ m α⟧ Q = wp⟦MonadLift.monadLift (MonadExceptOf.throw (ε:=ε) e : m α) : ReaderT ρ m α⟧ Q := rfl

@[simp]
theorem throw_StateT [WP m sh] [Monad m] [MonadExceptOf ε m] :
  wp⟦MonadExceptOf.throw (ε:=ε) e : StateT ρ m α⟧ Q = wp⟦MonadLift.monadLift (MonadExceptOf.throw (ε:=ε) e : m α) : StateT ρ m α⟧ Q := rfl

-- The following lemma is structurally different to StateT and others because of weird definitions
-- for lifting throw
@[simp]
theorem throw_lift_ExceptT [WP m sh] [Monad m] [MonadExceptOf ε m] :
    wp⟦MonadExceptOf.throw (ε:=ε) e : ExceptT ε' m α⟧ Q = wp⟦MonadExceptOf.throw (ε:=ε) e : m (Except ε' α)⟧ (fun | .ok a => Q.1 a | .error e => Q.2.1 e, Q.2.2) := by
  simp only [wp, MonadExceptOf.throw, PredTrans.pushExcept_apply]
  congr
  ext x
  split <;> rfl

@[simp]
theorem tryCatch_MonadExcept [MonadExceptOf ε m] [WP m ps] :
  wp⟦tryCatch x h : m α⟧ Q = wp⟦MonadExceptOf.tryCatch x h : m α⟧ Q := rfl

@[simp]
theorem tryCatchThe [MonadExceptOf ε m] [WP m ps] :
  wp⟦tryCatchThe ε x h : m α⟧ Q = wp⟦MonadExceptOf.tryCatch x h : m α⟧ Q := rfl

@[simp]
theorem tryCatch_Except :
    wp⟦MonadExceptOf.tryCatch x h : Except ε α⟧ Q = wp⟦x⟧ (Q.1, fun e => wp⟦h e⟧ Q, Q.2.2) := by
  simp only [wp, PredTrans.pure, Id.run, MonadExceptOf.tryCatch, Except.tryCatch,
    PredTrans.pushExcept_apply]
  cases x <;> simp

@[simp]
theorem tryCatch_ExceptT [Monad m] [WPMonad m ps] :
    wp⟦MonadExceptOf.tryCatch x h : ExceptT ε m α⟧ Q = wp⟦x⟧ (Q.1, fun e => wp⟦h e⟧ Q, Q.2.2) := by
  simp only [wp, MonadExceptOf.tryCatch, ExceptT.tryCatch, ExceptT.mk, bind, PredTrans.pushExcept_apply]
  congr
  ext x
  split <;> simp

open EStateM.Backtrackable in
@[simp]
theorem tryCatch_EStateM {ε σ δ α x h Q} [EStateM.Backtrackable δ σ]:
    wp⟦MonadExceptOf.tryCatch x h : EStateM ε σ α⟧ Q = fun s => wp⟦x⟧ (Q.1, fun e s' => wp⟦h e⟧ Q (restore s' (save s)), Q.2.2) s := by
  ext s
  simp only [wp, MonadExceptOf.tryCatch, EStateM.tryCatch]
  cases x s <;> simp

@[simp]
theorem tryCatch_ReaderT [WP m sh] [Monad m] [MonadExceptOf ε m] :
    wp⟦MonadExceptOf.tryCatch (ε:=ε) x h : ReaderT ρ m α⟧ Q = fun r => wp⟦MonadExceptOf.tryCatch (ε:=ε) (x.run r) (fun e => (h e).run r) : m α⟧ (fun a => Q.1 a r, Q.2) := by
  simp [wp, MonadExceptOf.tryCatch, tryCatchThe, ReaderT.run]

@[simp]
theorem tryCatch_StateT [WP m sh] [Monad m] [MonadExceptOf ε m] :
    wp⟦MonadExceptOf.tryCatch (ε:=ε) x h : StateT σ m α⟧ Q = fun s => wp⟦MonadExceptOf.tryCatch (ε:=ε) (x.run s) (fun e => (h e).run s) : m (α × σ)⟧ (fun xs => Q.1 xs.1 xs.2, Q.2) := by
  simp [wp, MonadExceptOf.tryCatch, tryCatchThe, StateT.run]

@[simp]
theorem tryCatch_lift_ExceptT [WP m sh] [Monad m] [MonadExceptOf ε m] :
    wp⟦MonadExceptOf.tryCatch (ε:=ε) x h : ExceptT ε' m α⟧ Q = wp⟦MonadExceptOf.tryCatch (ε:=ε) x h : m (Except ε' α)⟧ (fun | .ok a => Q.1 a | .error e => Q.2.1 e, Q.2.2) := by
  simp only [wp, MonadExceptOf.tryCatch, tryCatchThe, PredTrans.pushExcept_apply, ExceptT.mk]
  congr
  ext x
  split <;> rfl

/-
example :
  wp (m:= ReaderT Char (StateT Bool (ExceptT Nat Id))) (do set true; throw 42; set false; get) =
  wp (m:= ReaderT Char (StateT Bool (ExceptT Nat Id))) (do set true; throw 42; get) := by
    ext Q : 4
    simp

example :
  wp (m:= ReaderT Char (StateT Bool (ExceptT Nat Id))) (do try { set true; throw 42 } catch _ => set false; get) =
  wp (m:= ReaderT Char (StateT Bool (ExceptT Nat Id))) (do set false; get) := by
    ext Q : 4
    simp
    -- This gets stuck because ExceptT.instMonad is not defeq to Except.instMonad and thus the `bind` rewrite does not apply.
    admit
-/

end MonadExceptOf
