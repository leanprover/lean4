/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Init.Data.Option.Basic
import Init.Control.Basic
import Init.Control.Except

set_option linter.missingDocs true

universe u v

instance : ToBool (Option α) := ⟨Option.isSome⟩

/--
Adds the ability to fail to a monad. Unlike ordinary exceptions, there is no way to signal why a
failure occurred.
-/
def OptionT (m : Type u → Type v) (α : Type u) : Type v :=
  m (Option α)

/--
Executes an action that might fail in the underlying monad `m`, returning `none` in case of failure.
-/
@[always_inline, inline]
def OptionT.run {m : Type u → Type v} {α : Type u} (x : OptionT m α) : m (Option α) :=
  x

namespace OptionT
variable {m : Type u → Type v} [Monad m] {α β : Type u}

/--
Converts an action that returns an `Option` into one that might fail, with `none` indicating
failure.
-/
protected def mk (x : m (Option α)) : OptionT m α :=
  x

/--
Sequences two potentially-failing actions. The second action is run only if the first succeeds.
-/
@[always_inline, inline]
protected def bind (x : OptionT m α) (f : α → OptionT m β) : OptionT m β := OptionT.mk do
  match (← x) with
  | some a => f a
  | none   => pure none

/--
Succeeds with the provided value.
-/
@[always_inline, inline]
protected def pure (a : α) : OptionT m α := OptionT.mk do
  pure (some a)

@[always_inline]
instance : Monad (OptionT m) where
  pure := OptionT.pure
  bind := OptionT.bind

instance {m : Type u → Type v} [Pure m] : Inhabited (OptionT m α) where
  default := pure (f:=m) default

/--
Recovers from failures. Typically used via the `<|>` operator.
-/
@[always_inline, inline] protected def orElse (x : OptionT m α) (y : Unit → OptionT m α) : OptionT m α := OptionT.mk do
  match (← x) with
  | some a => pure (some a)
  | _      => y ()

/--
A recoverable failure.
-/
@[always_inline, inline] protected def fail : OptionT m α := OptionT.mk do
  pure none

instance : Alternative (OptionT m) where
  failure := OptionT.fail
  orElse  := OptionT.orElse

/--
Converts a computation from the underlying monad into one that could fail, even though it does not.

This function is typically implicitly accessed via a `MonadLiftT` instance as part of [automatic
lifting](lean-manual://section/monad-lifting).
-/
@[always_inline, inline] protected def lift (x : m α) : OptionT m α := OptionT.mk do
  return some (← x)

instance : MonadLift m (OptionT m) := ⟨OptionT.lift⟩

instance : MonadFunctor m (OptionT m) := ⟨fun f x => f x⟩

/--
Handles failures by treating them as exceptions of type `Unit`.
-/
@[always_inline, inline] protected def tryCatch (x : OptionT m α) (handle : Unit → OptionT m α) : OptionT m α := OptionT.mk do
  let some a ← x | handle ()
  pure a

instance : MonadExceptOf Unit (OptionT m) where
  throw    := fun _ => OptionT.fail
  tryCatch := OptionT.tryCatch

instance (ε : Type u) [MonadExceptOf ε m] : MonadExceptOf ε (OptionT m) where
  throw e           := OptionT.mk <| throwThe ε e
  tryCatch x handle := OptionT.mk <| tryCatchThe ε x handle

end OptionT

instance [Monad m] : MonadControl m (OptionT m) where
  stM        := Option
  liftWith f := liftM <| f fun x => x.run
  restoreM x := x
