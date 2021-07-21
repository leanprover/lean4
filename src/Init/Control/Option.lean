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
variable {m : Type u → Type v} {α β : Type u}

protected def mk (x : m (Option α)) : OptionT m α :=
  x

@[inline] protected def map [Functor m] (f : α → β) (x : OptionT m α) : OptionT m β :=
  OptionT.mk <| Option.map f <$> x.run 

instance [Functor m] : Functor (OptionT m) where 
  map := OptionT.map

@[inline] protected def pure [Pure m] (a : α) : OptionT m α := OptionT.mk do
  pure (some a)

instance [Pure m] : Pure (OptionT m) := ⟨OptionT.pure⟩

@[inline] protected def bind [Monad m] (x : OptionT m α) (f : α → OptionT m β) : OptionT m β := OptionT.mk do
  match (← x) with
  | some a => f a
  | none   => pure none

instance [Monad m] : Monad (OptionT m) where
  pure := OptionT.pure
  bind := OptionT.bind

@[inline] protected def orElse [Monad m] (x : OptionT m α) (y : OptionT m α) : OptionT m α := OptionT.mk do
  match (← x) with
  | some a => pure (some a)
  | _      => y

@[inline] protected def fail [Pure m] : OptionT m α := OptionT.mk do
  pure none

instance [Monad m] : Alternative (OptionT m) where
  failure := OptionT.fail
  orElse  := OptionT.orElse

@[inline] protected def lift [Functor m] (x : m α) : OptionT m α := 
  OptionT.mk <| some <$> x

instance [Functor m] : MonadLift m (OptionT m) := ⟨OptionT.lift⟩

instance : MonadFunctor m (OptionT m) := ⟨fun f x => f x⟩

@[inline] protected def tryCatch [Monad m] (x : OptionT m α) (handle : Unit → OptionT m α) : OptionT m α := OptionT.mk do
  let some a ← x | handle ()
  pure a

instance [Monad m] : MonadExceptOf Unit (OptionT m) where
  throw    := fun _ => OptionT.fail
  tryCatch := OptionT.tryCatch

instance (ε : Type u) [Monad m] [MonadExceptOf ε m] : MonadExceptOf ε (OptionT m) where
  throw e           := OptionT.mk <| throwThe ε e
  tryCatch x handle := OptionT.mk <| tryCatchThe ε x handle

end OptionT

abbrev OptionM (α : Type u) := OptionT Id α

abbrev OptionM.run (x : OptionM α) : Option α :=
  x
