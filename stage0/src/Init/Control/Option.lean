/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Init.Data.Option.Basic
import Init.Control.Basic
import Init.Control.Except

universe u v

instance {α} : ToBool (Option α) := ⟨Option.toBool⟩

def OptionT (m : Type u → Type v) (α : Type u) : Type v :=
  m (Option α)

@[inline] def OptionT.run {m : Type u → Type v} {α : Type u} (x : OptionT m α) : m (Option α) :=
  x

namespace OptionT
variable {m : Type u → Type v} [Monad m] {α β : Type u}

@[inline] protected def bind (x : OptionT m α) (f : α → OptionT m β) : OptionT m β := id (α := m (Option β)) do
  match (← x) with
  | some a => f a
  | none   => pure none

@[inline] protected def pure (a : α) : OptionT m α := id (α := m (Option α)) do
  pure (some a)

instance : Monad (OptionT m) := {
  pure := OptionT.pure
  bind := OptionT.bind
}

@[inline] protected def orElse (x : OptionT m α) (y : OptionT m α) : OptionT m α := id (α := m (Option α)) do
  match (← x) with
  | some a => pure (some a)
  | _      => y

@[inline] protected def fail : OptionT m α := id (α := m (Option α)) do
  pure none

instance : Alternative (OptionT m) := {
  failure := OptionT.fail
  orElse  := OptionT.orElse
}

@[inline] protected def lift (x : m α) : OptionT m α := id (α := m (Option α)) do
  return some (← x)

instance : MonadLift m (OptionT m) := ⟨OptionT.lift⟩

instance : MonadFunctor m (OptionT m) := ⟨fun f x => f x⟩

@[inline] protected def tryCatch (x : OptionT m α) (handle : Unit → OptionT m α) : OptionT m α := id (α := m (Option α)) do
  let some a ← x | handle ()
  pure a

instance : MonadExceptOf Unit (OptionT m) := {
  throw    := fun _ => OptionT.fail
  tryCatch := OptionT.tryCatch
}

end OptionT

abbrev OptionM (α : Type u) := OptionT Id α

abbrev OptionM.run (x : OptionM α) : Option α :=
  x
