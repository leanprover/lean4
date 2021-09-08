/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Init.Core

universe u v w

@[reducible] def Functor.mapRev {f : Type u → Type v} [Functor f] {α β : Type u} : f α → (α → β) → f β :=
  fun a f => f <$> a

infixr:100 " <&> " => Functor.mapRev

@[inline] def Functor.discard {f : Type u → Type v} {α : Type u} [Functor f] (x : f α) : f PUnit :=
  Functor.mapConst PUnit.unit x

export Functor (discard)

class Alternative (f : Type u → Type v) extends Applicative f : Type (max (u+1) v) where
  failure : {α : Type u} → f α
  orElse  : {α : Type u} → f α → (Unit → f α) → f α

instance (f : Type u → Type v) (α : Type u) [Alternative f] : OrElse (f α) := ⟨Alternative.orElse⟩

variable {f : Type u → Type v} [Alternative f] {α : Type u}

export Alternative (failure)

@[inline] def guard {f : Type → Type v} [Alternative f] (p : Prop) [Decidable p] : f Unit :=
  if p then pure () else failure

@[inline] def optional (x : f α) : f (Option α) :=
  some <$> x <|> pure none

class ToBool (α : Type u) where
  toBool : α → Bool

export ToBool (toBool)

instance : ToBool Bool where
  toBool b := b

@[macroInline] def bool {β : Type u} {α : Type v} [ToBool β] (f t : α) (b : β) : α :=
  match toBool b with
  | true  => t
  | false => f

@[macroInline] def orM {m : Type u → Type v} {β : Type u} [Monad m] [ToBool β] (x y : m β) : m β := do
  let b ← x
  match toBool b with
  | true  => pure b
  | false => y

infixr:30 " <||> " => orM

@[macroInline] def andM {m : Type u → Type v} {β : Type u} [Monad m] [ToBool β] (x y : m β) : m β := do
  let b ← x
  match toBool b with
  | true  => y
  | false => pure b

infixr:35 " <&&> " => andM

@[macroInline] def notM {m : Type → Type v} [Applicative m] (x : m Bool) : m Bool :=
  not <$> x

class MonadControl (m : Type u → Type v) (n : Type u → Type w) where
  stM      : Type u → Type u
  liftWith : {α : Type u} → (({β : Type u} → n β → m (stM β)) → m α) → n α
  restoreM : {α : Type u} → m (stM α) → n α

class MonadControlT (m : Type u → Type v) (n : Type u → Type w) where
  stM      : Type u → Type u
  liftWith : {α : Type u} → (({β : Type u} → n β → m (stM β)) → m α) → n α
  restoreM {α : Type u} : stM α → n α

export MonadControlT (stM liftWith restoreM)

instance (m n o) [MonadControl n o] [MonadControlT m n] : MonadControlT m o where
  stM α := stM m n (MonadControl.stM n o α)
  liftWith f := MonadControl.liftWith fun x₂ => liftWith fun x₁ => f (x₁ ∘ x₂)
  restoreM := MonadControl.restoreM ∘ restoreM

instance (m : Type u → Type v) [Pure m] : MonadControlT m m where
  stM α := α
  liftWith f := f fun x => x
  restoreM x := pure x

@[inline]
def controlAt (m : Type u → Type v) {n : Type u → Type w} [s1 : MonadControlT m n] [s2 : Bind n] {α : Type u}
    (f : ({β : Type u} → n β → m (stM m n β)) → m (stM m n α)) : n α :=
  liftWith f >>= restoreM

@[inline]
def control {m : Type u → Type v} {n : Type u → Type w} [MonadControlT m n] [Bind n] {α : Type u}
    (f : ({β : Type u} → n β → m (stM m n β)) → m (stM m n α)) : n α :=
  controlAt m f

/-
  Typeclass for the polymorphic `forM` operation described in the "do unchained" paper.
  Remark:
  - `γ` is a "container" type of elements of type `α`.
  - `α` is treated as an output parameter by the typeclass resolution procedure.
    That is, it tries to find an instance using only `m` and `γ`.
-/
class ForM (m : Type u → Type v) (γ : Type w₁) (α : outParam (Type w₂)) where
  forM [Monad m] : γ → (α → m PUnit) → m PUnit

export ForM (forM)
