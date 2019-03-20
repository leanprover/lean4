/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jared Roesch, Sebastian Ullrich

The except monad transformer.
-/
prelude
import init.control.alternative init.control.lift init.data.toString
import init.control.monadFail
universes u v w

inductive except (ε : Type u) (α : Type v)
| error {} : ε → except
| ok {} : α → except

instance {ε α : Type} [inhabited ε] : inhabited (except ε α) :=
⟨except.error (default ε)⟩

section
variables {ε : Type u} {α : Type v}

protected def except.toString [hasToString ε] [hasToString α] : except ε α → string
| (except.error e) := "(error " ++ toString e ++ ")"
| (except.ok a)    := "(ok " ++ toString a ++ ")"

protected def except.repr [hasRepr ε] [hasRepr α] : except ε α → string
| (except.error e) := "(error " ++ repr e ++ ")"
| (except.ok a)    := "(ok " ++ repr a ++ ")"

instance [hasToString ε] [hasToString α] : hasToString (except ε α) :=
⟨except.toString⟩

instance [hasRepr ε] [hasRepr α] : hasRepr (except ε α) :=
⟨except.repr⟩
end

namespace except
variables {ε : Type u}

@[inline] protected def return {α : Type v} (a : α) : except ε α :=
except.ok a

@[inline] protected def map {α β : Type v} (f : α → β) : except ε α → except ε β
| (except.error err) := except.error err
| (except.ok v) := except.ok $ f v

@[inline] protected def mapError {ε' : Type u} {α : Type v} (f : ε → ε') : except ε α → except ε' α
| (except.error err) := except.error $ f err
| (except.ok v) := except.ok v

@[inline] protected def bind {α β : Type v} (ma : except ε α) (f : α → except ε β) : except ε β :=
match ma with
| (except.error err) := except.error err
| (except.ok v) := f v

@[inline] protected def toBool {α : Type v} : except ε α → bool
| (except.ok _)    := tt
| (except.error _) := ff

@[inline] protected def toOption {α : Type v} : except ε α → option α
| (except.ok a)    := some a
| (except.error _) := none

@[inline] protected def catch {α : Type u} (ma : except ε α) (handle : ε → except ε α) : except ε α :=
match ma with
| except.ok a    := except.ok a
| except.error e := handle e

instance : monad (except ε) :=
{ pure := @except.return _, bind := @except.bind _ }
end except

def exceptT (ε : Type u) (m : Type u → Type v) (α : Type u) : Type v :=
m (except ε α)

@[inline] def exceptT.mk {ε : Type u} {m : Type u → Type v} {α : Type u} (x : m (except ε α)) : exceptT ε m α :=
x

@[inline] def exceptT.run {ε : Type u} {m : Type u → Type v} {α : Type u} (x : exceptT ε m α) : m (except ε α) :=
x

namespace exceptT
variables {ε : Type u} {m : Type u → Type v} [monad m]

@[inline] protected def return {α : Type u} (a : α) : exceptT ε m α :=
exceptT.mk $ pure (except.ok a)

@[inline] protected def bindCont {α β : Type u} (f : α → exceptT ε m β) : except ε α → m (except ε β)
| (except.ok a)    := f a
| (except.error e) := pure (except.error e)

@[inline] protected def bind {α β : Type u} (ma : exceptT ε m α) (f : α → exceptT ε m β) : exceptT ε m β :=
exceptT.mk $ ma >>= exceptT.bindCont f

@[inline] protected def lift {α : Type u} (t : m α) : exceptT ε m α :=
exceptT.mk $ except.ok <$> t

instance exceptTOfExcept : hasMonadLift (except ε) (exceptT ε m) :=
⟨λ α e, exceptT.mk $ pure e⟩

instance : hasMonadLift m (exceptT ε m) :=
⟨@exceptT.lift _ _ _⟩

@[inline] protected def catch {α : Type u} (ma : exceptT ε m α) (handle : ε → exceptT ε m α) : exceptT ε m α :=
exceptT.mk $ ma >>= λ res, match res with
 | except.ok a    := pure (except.ok a)
 | except.error e := (handle e)

instance (m') [monad m'] : monadFunctor m m' (exceptT ε m) (exceptT ε m') :=
⟨λ _ f x, f x⟩

instance : monad (exceptT ε m) :=
{ pure := @exceptT.return _ _ _, bind := @exceptT.bind _ _ _ }

@[inline] protected def adapt {ε' α : Type u} (f : ε → ε') : exceptT ε m α → exceptT ε' m α :=
λ x, exceptT.mk $ except.mapError f <$> x
end exceptT

/-- An implementation of [MonadError](https://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-Except.html#t:MonadError) -/
class monadExcept (ε : outParam (Type u)) (m : Type v → Type w) :=
(throw {} {α : Type v} : ε → m α)
(catch {} {α : Type v} : m α → (ε → m α) → m α)

namespace monadExcept
variables {ε : Type u} {m : Type v → Type w}

@[inline] protected def orelse [monadExcept ε m] {α : Type v} (t₁ t₂ : m α) : m α :=
catch t₁ $ λ _, t₂

/-- Alternative orelse operator that allows to select which exception should be used.
    The default is to use the first exception since the standard `orelse` uses the second. -/
@[inline] def orelse' [monadExcept ε m] {α : Type v} (t₁ t₂ : m α) (useFirstEx := tt) : m α :=
catch t₁ $ λ e₁, catch t₂ $ λ e₂, throw (if useFirstEx then e₁ else e₂)

@[inline] def liftExcept {ε' : Type u} [monadExcept ε m] [hasLiftT ε' ε] [monad m] {α : Type v} : except ε' α → m α
| (except.error e) := throw ↑e
| (except.ok a)    := pure a
end monadExcept

export monadExcept (throw catch)

instance (m : Type u → Type v) (ε : Type u) [monad m] : monadExcept ε (exceptT ε m) :=
{ throw := λ α e, exceptT.mk $ pure (except.error e),
  catch := @exceptT.catch ε _ _ }

instance (ε) : monadExcept ε (except ε) :=
{ throw := λ α, except.error, catch := @except.catch _ }

/-- Adapt a monad stack, changing its top-most error type.

    Note: This class can be seen as a simplification of the more "principled" definition
    ```
    class monadExceptFunctor (ε ε' : outParam (Type u)) (n n' : Type u → Type u) :=
    (map {} {α : Type u} : (∀ {m : Type u → Type u} [monad m], exceptT ε m α → exceptT ε' m α) → n α → n' α)
    ```
-/
class monadExceptAdapter (ε ε' : outParam (Type u)) (m m' : Type u → Type v) :=
(adaptExcept {} {α : Type u} : (ε → ε') → m α → m' α)
export monadExceptAdapter (adaptExcept)

section
variables {ε ε' : Type u} {m m' : Type u → Type v}

instance monadExceptAdapterTrans {n n' : Type u → Type v} [monadFunctor m m' n n'] [monadExceptAdapter ε ε' m m'] : monadExceptAdapter ε ε' n n' :=
⟨λ α f, monadMap (λ α, (adaptExcept f : m α → m' α))⟩

instance [monad m] : monadExceptAdapter ε ε' (exceptT ε m) (exceptT ε' m) :=
⟨λ α, exceptT.adapt⟩
end

instance (ε m out) [monadRun out m] : monadRun (λ α, out (except ε α)) (exceptT ε m) :=
⟨λ α, run⟩

-- useful for implicit failures in do-notation
instance (m : Type → Type) [monad m] : monadFail (exceptT string m) :=
⟨λ _, throw⟩
