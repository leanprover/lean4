/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Core
import Init.Control.Basic
import Init.Coe

namespace Option

def toMonad [Monad m] [Alternative m] : Option α → m α
  | none     => failure
  | some a   => pure a

@[inline] def toBool : Option α → Bool
  | some _ => true
  | none   => false

@[inline] def isSome : Option α → Bool
  | some _ => true
  | none   => false

@[inline] def isNone : Option α → Bool
  | some _ => false
  | none   => true

@[inline] def isEqSome [BEq α] : Option α → α → Bool
  | some a, b => a == b
  | none,   _ => false

@[inline] protected def bind : Option α → (α → Option β) → Option β
  | none,   _ => none
  | some a, b => b a

@[inline] protected def map (f : α → β) (o : Option α) : Option β :=
  Option.bind o (some ∘ f)

@[inline] protected def mapM [Monad m] (f : α → m β) (o : Option α) : m (Option β) := do
  if let some a := o then
    return some (← f a)
  else
    return none

theorem map_id : (Option.map id : Option α → Option α) = id :=
  funext (fun o => match o with | none => rfl | some _ => rfl)

instance : Functor Option where
  map := Option.map

@[inline] protected def filter (p : α → Bool) : Option α → Option α
  | some a => if p a then some a else none
  | none   => none

@[inline] protected def all (p : α → Bool) : Option α → Bool
  | some a => p a
  | none   => true

@[inline] protected def any (p : α → Bool) : Option α → Bool
  | some a => p a
  | none   => false

@[macroInline] protected def orElse : Option α → (Unit → Option α) → Option α
  | some a, _ => some a
  | none,   b => b ()

instance : OrElse (Option α) where
  orElse := Option.orElse

@[inline] protected def lt (r : α → α → Prop) : Option α → Option α → Prop
  | none, some _     => True
  | some x,   some y => r x y
  | _, _             => False

instance (r : α → α → Prop) [s : DecidableRel r] : DecidableRel (Option.lt r)
  | none,   some _ => isTrue  trivial
  | some x, some y => s x y
  | some _, none   => isFalse not_false
  | none,   none   => isFalse not_false

end Option

deriving instance DecidableEq for Option
deriving instance BEq for Option

instance [LT α] : LT (Option α) where
  lt := Option.lt (· < ·)

instance : Functor Option where
  map := Option.map

instance : Monad Option where
  pure := Option.some
  bind := Option.bind

instance : Alternative Option where
  failure := Option.none
  orElse  := Option.orElse

def liftOption [Alternative m] : Option α → m α
  | some a => pure a
  | none   => failure

@[inline] protected def Option.tryCatch (x : Option α) (handle : Unit → Option α) : Option α :=
  match x with
  | some _ => x
  | none => handle ()

instance : MonadExceptOf Unit Option where
  throw    := fun _ => Option.none
  tryCatch := Option.tryCatch
