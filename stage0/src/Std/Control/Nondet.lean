/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

/-
NondetT monad transformer.
It is uses `unsafe` features to workaround the positivity constraints
in the definition of `Alts`.
-/
namespace Std
namespace NondetT

universe u

private def AltsCore := PNonScalar.{u}

inductive Alts (m : Type u → Type u) (α : Type u)
| nil                                  : Alts m α
| cons  (head : α) (tail : m AltsCore) : Alts m α
| delayed (t : Thunk (m AltsCore))     : Alts m α

namespace Alts

variable {m : Type u → Type u} {α : Type u}

@[inline]
unsafe def ofAltsCore (x : m AltsCore.{u}) : m (Alts m α) :=
  unsafeCast x

@[inline]
unsafe def toAltsCore (x : m (Alts m α)) : m AltsCore.{u} :=
  unsafeCast x

mutual
unsafe def run' [Monad m] : Alts m α → m (Option (α × m (Alts m α)))
  | nil        => pure none
  | cons x xs  => pure $ some (x, ofAltsCore xs)
  | delayed xs => runUnsafe (ofAltsCore xs.get)

unsafe def runUnsafe [Monad m] (x : m (Alts m α)) : m (Option (α × m (Alts m α))) := do
  run' (← x)
end

unsafe def ofList [Monad m] : List α → m (Alts m α)
  | []    => pure Alts.nil
  | a::as => pure $ Alts.cons a (toAltsCore (ofList as))

mutual
unsafe def append' [Monad m] : Alts m α → (Unit → m (Alts m α)) → m (Alts m α)
  | nil,          bs => bs ()
  | cons a as,    bs => pure $ delayed $ Thunk.mk fun _ => toAltsCore $ pure $ cons a $ toAltsCore $ append (ofAltsCore as) bs
  | delayed as,   bs => pure $ delayed $ Thunk.mk fun _ => toAltsCore $ append (ofAltsCore as.get) bs

unsafe def append [Monad m] (xs : m (Alts m α)) (ys : Unit → m (Alts m α)) : m (Alts m α) := do
  append' (← xs) ys
end

mutual
unsafe def join' [Monad m] : Alts m (m (Alts m α)) → m (Alts m α)
  | nil        => pure nil
  | cons x xs  => pure $ delayed $ Thunk.mk fun _ => toAltsCore $ append x fun _ =>join $ ofAltsCore xs
  | delayed xs => pure $ delayed $ Thunk.mk fun _ => toAltsCore (α := α) $ join (ofAltsCore xs.get)

unsafe def join [Monad m] (xs : m (Alts m (m (Alts m α)))) : m (Alts m α) := do
  join' (← xs)
end

mutual
unsafe def map' [Monad m] (f : α → β) : Alts m α → m (Alts m β)
  | nil          => pure nil
  | cons x xs    => pure $ delayed $ Thunk.mk fun _ => toAltsCore $ pure $ cons (f x) $ toAltsCore $ map f (ofAltsCore xs)
  | delayed xs   => pure $ delayed $ Thunk.mk fun _ => toAltsCore $ map f (ofAltsCore xs.get)

unsafe def map [Monad m] (f : α → β) (xs : m (Alts m α)) : m (Alts m β) := do
  map' f (← xs)
end

@[inline]
protected unsafe def pure [Monad m] (a : α) : m (Alts m α) := do
  pure $ Alts.cons a $ toAltsCore (α := α) Alts.nil

end Alts
end NondetT

open NondetT (Alts)

def NondetT (m : Type u → Type u) (α : Type u) := m (Alts m α)

namespace NondetT
instance [Pure m] : Inhabited (NondetT m α) where
  default := (pure Alts.nil : m (Alts m α))

@[inline]
unsafe def appendUnsafe [Monad m] (x : NondetT m α) (y : Unit → NondetT m α) : NondetT m α :=
  Alts.append x y

@[implementedBy appendUnsafe]
protected constant append [Monad m] (x : NondetT m α) (y : Unit → NondetT m α) : NondetT m α

@[inline]
unsafe def joinUnsafe [Monad m] (x : NondetT m (NondetT m α)) : NondetT m α :=
  Alts.join x

@[implementedBy joinUnsafe]
protected constant join [Monad m] (x : NondetT m (NondetT m α)) : NondetT m α

@[inline]
unsafe def mapUnsafe [Monad m] (f : α → β) (x : NondetT m α) : NondetT m β :=
  Alts.map f x

@[implementedBy mapUnsafe]
protected constant map [Monad m] (f : α → β) (x : NondetT m α) : NondetT m β

@[inline]
unsafe def pureUnsafe [Monad m] (a : α) : NondetT m α :=
  Alts.pure a

@[implementedBy pureUnsafe]
protected constant pure [Monad m] (a : α) : NondetT m α

@[inline]
protected def failure [Monad m] : NondetT m α := id (α := m (Alts m α)) $
  pure Alts.nil

instance [Monad m] : Monad (NondetT m) where
  bind x f := NondetT.join (NondetT.map f x)
  pure     := NondetT.pure
  map      := NondetT.map

instance [Monad m] : Alternative (NondetT m) where
  failure := NondetT.failure
  orElse  := NondetT.append

@[inline]
unsafe def runUnsafe [Monad m] (x : NondetT m α) : m (Option (α × NondetT m α)) :=
  Alts.runUnsafe x

@[implementedBy runUnsafe]
protected constant run [Monad m] (x : NondetT m α) : m (Option (α × NondetT m α))

protected def run' [Monad m] (x : NondetT m α) : m (Option α) := do
  match (← x.run) with
  | some (a, _) => pure (some a)
  | none        => pure none

@[inline]
unsafe def chooseUnsafe [Monad m] (as : List α) : NondetT m α :=
  Alts.ofList as

@[implementedBy chooseUnsafe]
constant chooseImp [Monad m] (as : List α) : NondetT m α

class Choose (m : Type u → Type u) :=
  (choose : List α → m α)

export Choose (choose)

instance [MonadLift m n] [Choose m] : Choose n where
  choose := fun as => liftM (m := m) $ choose as

instance [Monad m] : Choose (NondetT m) where
  choose := chooseImp

@[inline]
unsafe def liftUnsafe [Monad m] (x : m α) : NondetT m α := id (α := m (Alts m α)) do
  let a ← x
  Alts.pure a

@[implementedBy liftUnsafe]
protected constant lift [Monad m] (x : m α) : NondetT m α

instance [Monad m] : MonadLift m (NondetT m) where
  monadLift := NondetT.lift

end NondetT
end Std
