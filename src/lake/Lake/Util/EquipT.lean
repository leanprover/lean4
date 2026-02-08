/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Init.Control.Except

namespace Lake

/--
A monad transformer that equips a monad with a value.
This is a generalization of `ReaderT` where the value is not
necessarily directly readable through the monad.
-/
@[expose] public def EquipT (ρ : Type u) (m : Type v → Type w) (α : Type v) :=
  ρ → m α

namespace EquipT

@[always_inline, inline] public def mk (x : ρ → m α) : EquipT ρ m α :=
  x

public instance [Inhabited (m α)] : Inhabited (EquipT ρ m α) where
  default := .mk fun _ => default

@[always_inline, inline] public def run (self : EquipT ρ m α) (r : ρ) : m α :=
  self r

@[always_inline, inline]
public protected def map [Functor m] (f : α → β) (self : EquipT ρ m α) : EquipT ρ m β :=
  fun r => Functor.map f (self r)

public instance [Functor m] : Functor (EquipT ρ m) where
  map := EquipT.map

@[always_inline, inline]
public protected def pure [Pure m] (a : α) : EquipT ρ m α :=
  fun _ => pure a

public instance [Pure m] : Pure (EquipT ρ m) := ⟨EquipT.pure⟩

@[always_inline, inline]
public def compose (f : m α₁ → (Unit → m α₂) → m β) (x₁ : EquipT ρ m α₁) (x₂ : Unit → EquipT ρ m α₂) : EquipT ρ m β :=
  fun r => f (x₁ r) (fun _ => x₂ () r)

@[always_inline, inline]
public protected def seq [Seq m] : EquipT ρ m (α → β) → (Unit → EquipT ρ m α) → EquipT ρ m β :=
  EquipT.compose Seq.seq

public instance [Seq m] : Seq (EquipT ρ m) := ⟨EquipT.seq⟩

public instance [Applicative m] : Applicative (EquipT ρ m)  := {}

@[always_inline, inline]
public protected def bind [Bind m] (self : EquipT ρ m α) (f : α → EquipT ρ m β) : EquipT ρ m β :=
  fun r => bind (self r) fun a => f a r

public instance [Bind m] : Bind (EquipT ρ m) := ⟨EquipT.bind⟩

public instance [Monad m] : Monad (EquipT ρ m) := {}

@[always_inline, inline]
public def lift (t : m α) : EquipT ρ m α :=
  fun _ => t

public instance : MonadLift m (EquipT ρ m) where
  monadLift := EquipT.lift

public instance : MonadFunctor m (EquipT ρ m) where
  monadMap f x := .mk fun ctx => f (x.run ctx)

@[always_inline, inline]
public protected def failure [Alternative m] : EquipT ρ m α :=
  fun _ => failure

@[always_inline, inline]
public protected def orElse [Alternative m] : EquipT ρ m α → (Unit → EquipT ρ m α) → EquipT ρ m α :=
  EquipT.compose Alternative.orElse

public instance [Alternative m] : Alternative (EquipT ρ m) where
  failure := EquipT.failure
  orElse  := EquipT.orElse

@[always_inline, inline]
public protected def throw [MonadExceptOf ε m]  (e : ε) : EquipT ρ m α  :=
  fun _ => throw e

@[always_inline, inline]
public protected def tryCatch [MonadExceptOf ε m]
  (self : EquipT ρ m α) (c : ε → EquipT ρ m α)
: EquipT ρ m α := fun f => tryCatchThe ε (self f) fun e => (c e) f

public instance (ε) [MonadExceptOf ε m] : MonadExceptOf ε (EquipT ρ m) where
  throw    := EquipT.throw
  tryCatch := EquipT.tryCatch

@[always_inline, inline]
public protected def tryFinally' [MonadFinally m] [Monad m]
  (x : EquipT ρ m α) (f : Option α → EquipT ρ m β)
: EquipT ρ m (α × β) := fun ctx => tryFinally' (x.run ctx) (fun a? => f a? |>.run ctx)

public instance [MonadFinally m] [Monad m] : MonadFinally (EquipT ρ m) := ⟨EquipT.tryFinally'⟩
