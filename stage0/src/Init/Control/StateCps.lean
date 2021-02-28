/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Control.Lawful

/-
The State monad transformer using CPS style.
-/

def StateCpsT (σ : Type u) (m : Type u → Type v) (α : Type u) := (δ : Type u) → σ → (α → σ → m δ) → m δ

namespace StateCpsT

@[inline] def run {α σ : Type u} {m : Type u → Type v} [Monad m] (x : StateCpsT σ m α) (s : σ) : m (α × σ) :=
  x _ s fun a s => pure (a, s)

@[inline] def run' {α σ : Type u} {m : Type u → Type v}  [Monad m] (x : StateCpsT σ m α) (s : σ) : m α :=
  (·.1) <$> run x s

@[inline] def runK {α σ : Type u} {m : Type u → Type v}  (x : StateCpsT σ m α) (s : σ) (k : α → σ → m β) : m β :=
  x _ s k

instance : Monad (StateCpsT σ m) where
  map  f x := fun δ s k => x δ s fun a s => k (f a) s
  pure a   := fun δ s k => k a s
  bind x f := fun δ s k => x δ s fun a s => f a δ s k

instance : LawfulMonad (StateCpsT σ m) := by
  refine! { .. } <;> intros <;> rfl

instance : MonadStateOf σ (StateCpsT σ m) where
  get   := fun δ s k => k s s
  set s := fun δ _ k => k ⟨⟩ s
  modifyGet f := fun _ s k => let (a, s) := f s; k a s

@[inline] protected def lift [Monad m] (x : m α) : StateCpsT σ m α :=
  fun _ s k => x >>= (k . s)

instance [Monad m] : MonadLift m (StateCpsT σ m) where
  monadLift := StateCpsT.lift

@[simp] theorem run'_eq [Monad m] (x : StateCpsT σ m α) (s : σ) : x.run' s = (·.1) <$> run x s := rfl

@[simp] theorem run_get [Monad m] (s : σ)  : (get : StateCpsT σ m σ).run s = pure (s, s) := rfl

@[simp] theorem run_set [Monad m] (s s' : σ) : (set s' : StateCpsT σ m PUnit).run s = pure (⟨⟩, s') := rfl

@[simp] theorem run_modify [Monad m] (f : σ → σ) (s : σ) : (modify f : StateCpsT σ m PUnit).run s = pure (⟨⟩, f s) := rfl

@[simp] theorem run_lift {α σ : Type u} [Monad m] (x : m α) (s : σ) : (StateCpsT.lift x : StateCpsT σ m α).run s = x >>= fun a => pure (a, s) := rfl

@[simp] theorem run_bind_pure {α σ : Type u} [Monad m] (a : α) (f : α → StateCpsT σ m β) (s : σ) : (pure a >>= f).run s = (f a).run s := rfl

@[simp] theorem run_bind_lift {α σ : Type u} [Monad m] (x : m α) (f : α → StateCpsT σ m β) (s : σ) : (StateCpsT.lift x >>= f).run s = x >>= fun a => (f a).run s := rfl

@[simp] theorem run_bind_get {σ : Type u} [Monad m] (f : σ → StateCpsT σ m β) (s : σ) : (get >>= f).run s = (f s).run s := rfl

@[simp] theorem run_bind_set {σ : Type u} [Monad m] (f : PUnit → StateCpsT σ m β) (s s' : σ) : (set s' >>= f).run s = (f ⟨⟩).run s' := rfl

@[simp] theorem run_bind_modify {σ : Type u} [Monad m] (f : σ → σ) (g : PUnit → StateCpsT σ m β) (s : σ) : (modify f >>= g).run s = (g ⟨⟩).run (f s) := rfl

@[simp] theorem run_monadLift {σ : Type u} [Monad m] [MonadLiftT n m] (x : n α) (s : σ) : (monadLift x : StateCpsT σ m α).run s = (monadLift x : m α) >>= fun a => pure (a, s) := rfl

@[simp] theorem run_pure [Monad m] (a : α) (s : σ) : (pure a : StateCpsT σ m α).run s = pure (a, s) := rfl

end StateCpsT
