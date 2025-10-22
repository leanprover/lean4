/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Init.Control.Lawful.Basic

public section

/-!
The Optionion monad transformer using CPS style.
-/

/--
Adds the ability to fail to a monad `m`.

Instead of using `Option` to model failures, this implementation uses continuation passing
style. This has different performance characteristics from `OptionT`.
-/
@[expose] def OptionCpsT (m : Type u → Type v) (α : Type u) := ⦃β : Type u⦄ → (α → m β) → (Unit → m β) → m β

namespace OptionCpsT

/--
Use a monadic action that may throw an exception as an action that may return an exception's value.
-/
@[always_inline, inline, expose]
def run {α : Type u} [Monad m] (x : OptionCpsT m α) : m (Option α) :=
  x (fun a => pure (some a)) (fun _ => pure none)

set_option linter.unusedVariables false in  -- `s` unused
/--
Use a monadic action that may throw an exception by providing explicit success and failure
continuations.
-/
@[always_inline, inline]
def runK {α : Type u} (x : OptionCpsT m α) (ok : α → m β) (error : Unit → m β) : m β :=
  x ok error

/--
Returns the value of a computation, forgetting whether it was a failure or a success.

This corresponds to early return.
-/
@[always_inline, inline, expose]
def runCatch [Monad m] (x : OptionCpsT m PUnit) : m PUnit :=
  x pure pure

@[always_inline]
instance : Monad (OptionCpsT m) where
  map f x  := fun _ k₁ k₂ => x (fun a => k₁ (f a)) k₂
  pure a   := fun _ k _ => k a
  bind x f := fun _ k₁ k₂ => x (fun a => f a k₁ k₂) k₂

instance : LawfulMonad (OptionCpsT m) := by
  refine LawfulMonad.mk' _ ?_ ?_ ?_ <;> intros <;> rfl

instance : MonadExceptOf PUnit (OptionCpsT m) where
  throw e  := fun _ _ k => k e
  tryCatch x handle := fun _ k₁ k₂ => x k₁ (fun e => handle e k₁ k₂)

/--
Run an action from the transformed monad in the exception monad.
-/
@[always_inline, inline, expose]
def lift [Monad m] (x : m α) : OptionCpsT m α :=
  fun _ k _ => x >>= k

instance [Monad m] : MonadLift m (OptionCpsT m) where
  monadLift := OptionCpsT.lift

instance : Inhabited (OptionCpsT m α) where
  default := fun _ _ k₂ => k₂ default

@[simp] theorem run_pure [Monad m] : run (pure x : OptionCpsT m α) = pure (some x) := rfl

@[simp] theorem run_lift {α : Type u} [Monad m] (x : m α) : run (OptionCpsT.lift x : OptionCpsT m α) = (x >>= fun a => pure (some a) : m (Option α)) := rfl

@[simp] theorem run_throw [Monad m] : run (throw e : OptionCpsT m β) = pure none := rfl

@[simp] theorem run_bind_lift [Monad m] (x : m α) (f : α → OptionCpsT m β) : run (OptionCpsT.lift x >>= f : OptionCpsT m β) = x >>= fun a => run (f a) := rfl

@[simp] theorem run_bind_throw [Monad m] (f : α → OptionCpsT m β) : run (throw e >>= f : OptionCpsT m β) = run (throw e) := rfl

@[simp] theorem runCatch_pure [Monad m] : runCatch (pure x : OptionCpsT m PUnit) = pure x := rfl

@[simp] theorem runCatch_lift [Monad m] [LawfulMonad m] (x : m PUnit) : runCatch (OptionCpsT.lift x : OptionCpsT m PUnit) = x := by
  simp [runCatch, lift]

@[simp] theorem runCatch_throw [Monad m] : runCatch (throw a : OptionCpsT m PUnit) = pure a := rfl

@[simp] theorem runCatch_bind_lift [Monad m] (x : m α) (f : α → OptionCpsT m PUnit) : runCatch (OptionCpsT.lift x >>= f : OptionCpsT m PUnit) = x >>= fun a => runCatch (f a) := rfl

@[simp] theorem runCatch_bind_throw [Monad m] (f : α → OptionCpsT m PUnit) : runCatch (throw e >>= f : OptionCpsT m PUnit) = pure e := rfl

end OptionCpsT
