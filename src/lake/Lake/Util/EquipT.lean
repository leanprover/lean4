/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Init.Control.Except

namespace Lake

/--
A monad transformer that equips a monad with a value.
This is a generalization of `ReaderT` where the value is not
necessarily directly readable through the monad.
-/
def EquipT (ρ : Type u) (m : Type v → Type w) (α : Type v) :=
  ρ → m α

variable {ρ : Type u} {m : Type v → Type w}

instance {α : Type v} [Inhabited (m α)] : Inhabited (EquipT ρ m α) where
  default := fun _ => default

namespace EquipT

@[inline] protected
def run {α : Type v} (self : EquipT ρ m α) (r : ρ) : m α :=
  self r

@[inline] protected
def map [Functor m] {α β : Type v} (f : α → β) (self : EquipT ρ m α) : EquipT ρ m β :=
  fun fetch => Functor.map f (self fetch)

instance [Functor m] : Functor (EquipT ρ m) where
  map := EquipT.map

@[inline] protected
def pure [Pure m] {α : Type v} (a : α) : EquipT ρ m α :=
  fun _ => pure a

instance [Pure m] : Pure (EquipT ρ m) where
  pure := EquipT.pure

@[inline] protected
def compose {α₁ α₂ β : Type v} (f : m α₁ → (Unit → m α₂) → m β) (x₁ : EquipT ρ m α₁) (x₂ : Unit → EquipT ρ m α₂) : EquipT ρ m β :=
  fun fetch => f (x₁ fetch) (fun _ => x₂ () fetch)

@[inline] protected
def seq [Seq m] {α β : Type v} : EquipT ρ m (α → β) → (Unit → EquipT ρ m α) → EquipT ρ m β :=
  EquipT.compose Seq.seq

instance [Seq m] : Seq (EquipT ρ m) where
  seq  := EquipT.seq

instance [Applicative m] : Applicative (EquipT ρ m)  := {}

@[inline] protected
def bind [Bind m] {α β : Type v} (self : EquipT ρ m α) (f : α → EquipT ρ m β) : EquipT ρ m β :=
  fun fetch => bind (self fetch) fun a => f a fetch

instance [Bind m] : Bind (EquipT ρ m) where
  bind := EquipT.bind

instance [Monad m] : Monad (EquipT ρ m) := {}

@[inline] protected
def lift {α : Type v} (t : m α) : EquipT ρ m α :=
  fun _ => t

instance : MonadLift m (EquipT ρ m) where
  monadLift := EquipT.lift

instance : MonadFunctor m (EquipT ρ m) where
  monadMap f x := fun ctx => f (x ctx)

@[inline] protected
def failure [Alternative m] {α : Type v} : EquipT ρ m α :=
  fun _ => failure

@[inline] protected
def orElse [Alternative m] {α : Type v} : EquipT ρ m α → (Unit → EquipT ρ m α) → EquipT ρ m α :=
  EquipT.compose Alternative.orElse

instance [Alternative m] : Alternative (EquipT ρ m) where
  failure := EquipT.failure
  orElse  := EquipT.orElse

@[inline] protected
def throw {ε : Type v} [MonadExceptOf ε m] {α : Type v} (e : ε) : EquipT ρ m α  :=
  fun _ => throw e

@[inline] protected
def tryCatch {ε : Type v} [MonadExceptOf ε m] {α : Type v} (self : EquipT ρ m α) (c : ε → EquipT ρ m α) : EquipT ρ m α :=
  fun f => tryCatchThe ε (self f) fun e => (c e) f

instance (ε) [MonadExceptOf ε m] : MonadExceptOf ε (EquipT ρ m) where
  throw    := EquipT.throw
  tryCatch := EquipT.tryCatch

@[always_inline]
instance [MonadFinally m] [Monad m] : MonadFinally (EquipT ρ m) where
  tryFinally' x h ctx := tryFinally' (x ctx) (fun a? => h a? ctx)
