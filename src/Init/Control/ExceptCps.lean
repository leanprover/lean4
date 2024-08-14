/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Control.Lawful.Basic

/-!
The Exception monad transformer using CPS style.
-/

def ExceptCpsT (ε : Type u) (m : Type u → Type v) (α : Type u) := (β : Type u) → (α → m β) → (ε → m β) → m β

namespace ExceptCpsT

@[always_inline, inline]
def run {ε α : Type u} [Monad m] (x : ExceptCpsT ε m α) : m (Except ε α) :=
  x _ (fun a => pure (Except.ok a)) (fun e => pure (Except.error e))

set_option linter.unusedVariables false in  -- `s` unused
@[always_inline, inline]
def runK {ε α : Type u} (x : ExceptCpsT ε m α) (s : ε) (ok : α → m β) (error : ε → m β) : m β :=
  x _ ok error

@[always_inline, inline]
def runCatch [Monad m] (x : ExceptCpsT α m α) : m α :=
  x α pure pure

@[always_inline]
instance : Monad (ExceptCpsT ε m) where
  map f x  := fun _ k₁ k₂ => x _ (fun a => k₁ (f a)) k₂
  pure a   := fun _ k _ => k a
  bind x f := fun _ k₁ k₂ => x _ (fun a => f a _ k₁ k₂) k₂

instance : LawfulMonad (ExceptCpsT σ m) := by
  refine LawfulMonad.mk' _ ?_ ?_ ?_ <;> intros <;> rfl

instance : MonadExceptOf ε (ExceptCpsT ε m) where
  throw e  := fun _ _ k => k e
  tryCatch x handle := fun _ k₁ k₂ => x _ k₁ (fun e => handle e _ k₁ k₂)

@[always_inline, inline]
def lift [Monad m] (x : m α) : ExceptCpsT ε m α :=
  fun _ k _ => x >>= k

instance [Monad m] : MonadLift m (ExceptCpsT σ m) where
  monadLift := ExceptCpsT.lift

instance [Inhabited ε] : Inhabited (ExceptCpsT ε m α) where
  default := fun _ _ k₂ => k₂ default

@[simp] theorem run_pure [Monad m] : run (pure x : ExceptCpsT ε m α) = pure (Except.ok x) := rfl

@[simp] theorem run_lift {α ε : Type u} [Monad m] (x : m α) : run (ExceptCpsT.lift x : ExceptCpsT ε m α) = (x >>= fun a => pure (Except.ok a) : m (Except ε α)) := rfl

@[simp] theorem run_throw [Monad m] : run (throw e : ExceptCpsT ε m β) = pure (Except.error e) := rfl

@[simp] theorem run_bind_lift [Monad m] (x : m α) (f : α → ExceptCpsT ε m β) : run (ExceptCpsT.lift x >>= f : ExceptCpsT ε m β) = x >>= fun a => run (f a) := rfl

@[simp] theorem run_bind_throw [Monad m] (e : ε) (f : α → ExceptCpsT ε m β) : run (throw e >>= f : ExceptCpsT ε m β) = run (throw e) := rfl

@[simp] theorem runCatch_pure [Monad m] : runCatch (pure x : ExceptCpsT α m α) = pure x := rfl

@[simp] theorem runCatch_lift {α : Type u} [Monad m] [LawfulMonad m] (x : m α) : runCatch (ExceptCpsT.lift x : ExceptCpsT α m α) = x := by
  simp [runCatch, lift]

@[simp] theorem runCatch_throw [Monad m] : runCatch (throw a : ExceptCpsT α m α) = pure a := rfl

@[simp] theorem runCatch_bind_lift [Monad m] (x : m α) (f : α → ExceptCpsT β m β) : runCatch (ExceptCpsT.lift x >>= f : ExceptCpsT β m β) = x >>= fun a => runCatch (f a) := rfl

@[simp] theorem runCatch_bind_throw [Monad m] (e : β) (f : α → ExceptCpsT β m β) : runCatch (throw e >>= f : ExceptCpsT β m β) = pure e := rfl

end ExceptCpsT
