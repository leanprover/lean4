/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jared Roesch, Sebastian Ullrich

The Except monad transformer.
-/
prelude
import init.control.alternative
import init.control.lift
import init.data.tostring
import init.control.monadfail
universes u v w

inductive Except (ε : Type u) (α : Type v)
| error {} : ε → Except
| ok {} : α → Except

attribute [unbox] Except

instance {ε α : Type} [Inhabited ε] : Inhabited (Except ε α) :=
⟨Except.error (default ε)⟩

section
variables {ε : Type u} {α : Type v}

protected def Except.toString [HasToString ε] [HasToString α] : Except ε α → String
| Except.error e => "(error " ++ toString e ++ ")"
| Except.ok a    => "(ok " ++ toString a ++ ")"

protected def Except.repr [HasRepr ε] [HasRepr α] : Except ε α → String
| Except.error e => "(error " ++ repr e ++ ")"
| Except.ok a    => "(ok " ++ repr a ++ ")"

instance [HasToString ε] [HasToString α] : HasToString (Except ε α) :=
⟨Except.toString⟩

instance [HasRepr ε] [HasRepr α] : HasRepr (Except ε α) :=
⟨Except.repr⟩
end

namespace Except
variables {ε : Type u}

@[inline] protected def return {α : Type v} (a : α) : Except ε α :=
Except.ok a

@[inline] protected def map {α β : Type v} (f : α → β) : Except ε α → Except ε β
| Except.error err => Except.error err
| Except.ok v => Except.ok $ f v

@[inline] protected def mapError {ε' : Type u} {α : Type v} (f : ε → ε') : Except ε α → Except ε' α
| Except.error err => Except.error $ f err
| Except.ok v => Except.ok v

@[inline] protected def bind {α β : Type v} (ma : Except ε α) (f : α → Except ε β) : Except ε β :=
match ma with
| (Except.error err) => Except.error err
| (Except.ok v)      => f v

@[inline] protected def toBool {α : Type v} : Except ε α → Bool
| Except.ok _    => true
| Except.error _ => false

@[inline] protected def toOption {α : Type v} : Except ε α → Option α
| Except.ok a    => some a
| Except.error _ => none

@[inline] protected def catch {α : Type u} (ma : Except ε α) (handle : ε → Except ε α) : Except ε α :=
match ma with
| Except.ok a    => Except.ok a
| Except.error e => handle e

instance : Monad (Except ε) :=
{ pure := @Except.return _, bind := @Except.bind _, map := @Except.map _ }
end Except

def ExceptT (ε : Type u) (m : Type u → Type v) (α : Type u) : Type v :=
m (Except ε α)

@[inline] def ExceptT.mk {ε : Type u} {m : Type u → Type v} {α : Type u} (x : m (Except ε α)) : ExceptT ε m α :=
x

@[inline] def ExceptT.run {ε : Type u} {m : Type u → Type v} {α : Type u} (x : ExceptT ε m α) : m (Except ε α) :=
x

namespace ExceptT
variables {ε : Type u} {m : Type u → Type v} [Monad m]

@[inline] protected def pure {α : Type u} (a : α) : ExceptT ε m α :=
ExceptT.mk $ pure (Except.ok a)

@[inline] protected def bindCont {α β : Type u} (f : α → ExceptT ε m β) : Except ε α → m (Except ε β)
| Except.ok a    => f a
| Except.error e => pure (Except.error e)

@[inline] protected def bind {α β : Type u} (ma : ExceptT ε m α) (f : α → ExceptT ε m β) : ExceptT ε m β :=
ExceptT.mk $ ma >>= ExceptT.bindCont f

@[inline] protected def map {α β : Type u} (f : α → β) (x : ExceptT ε m α) : ExceptT ε m β :=
ExceptT.mk $ x >>= fun a => match a with
  | (Except.ok a)    => pure $ Except.ok (f a)
  | (Except.error e) => pure $ Except.error e

@[inline] protected def lift {α : Type u} (t : m α) : ExceptT ε m α :=
ExceptT.mk $ Except.ok <$> t

instance exceptTOfExcept : HasMonadLift (Except ε) (ExceptT ε m) :=
⟨fun α e => ExceptT.mk $ pure e⟩

instance : HasMonadLift m (ExceptT ε m) :=
⟨@ExceptT.lift _ _ _⟩

@[inline] protected def catch {α : Type u} (ma : ExceptT ε m α) (handle : ε → ExceptT ε m α) : ExceptT ε m α :=
ExceptT.mk $ ma >>= fun res => match res with
 | Except.ok a    => pure (Except.ok a)
 | Except.error e => (handle e)

instance (m') [Monad m'] : MonadFunctor m m' (ExceptT ε m) (ExceptT ε m') :=
⟨fun _ f x => f x⟩

instance : Monad (ExceptT ε m) :=
{ pure := @ExceptT.pure _ _ _, bind := @ExceptT.bind _ _ _, map := @ExceptT.map _ _ _ }

@[inline] protected def adapt {ε' α : Type u} (f : ε → ε') : ExceptT ε m α → ExceptT ε' m α :=
fun x => ExceptT.mk $ Except.mapError f <$> x
end ExceptT

/-- An implementation of [MonadError](https://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-Except.html#t:MonadError) -/
class MonadExcept (ε : outParam (Type u)) (m : Type v → Type w) :=
(throw {} {α : Type v} : ε → m α)
(catch {} {α : Type v} : m α → (ε → m α) → m α)

namespace MonadExcept
variables {ε : Type u} {m : Type v → Type w}

@[inline] protected def orelse [MonadExcept ε m] {α : Type v} (t₁ t₂ : m α) : m α :=
catch t₁ $ fun _ => t₂

/-- Alternative orelse operator that allows to select which exception should be used.
    The default is to use the first exception since the standard `orelse` uses the second. -/
@[inline] def orelse' [MonadExcept ε m] {α : Type v} (t₁ t₂ : m α) (useFirstEx := true) : m α :=
catch t₁ $ fun e₁ => catch t₂ $ fun e₂ => throw (if useFirstEx then e₁ else e₂)

@[inline] def liftExcept {ε' : Type u} [MonadExcept ε m] [HasLiftT ε' ε] [Monad m] {α : Type v} : Except ε' α → m α
| Except.error e => throw (coe e)
| Except.ok a    => pure a
end MonadExcept

export MonadExcept (throw catch)

instance (m : Type u → Type v) (ε : Type u) [Monad m] : MonadExcept ε (ExceptT ε m) :=
{ throw := fun α e => ExceptT.mk $ pure (Except.error e),
  catch := @ExceptT.catch ε _ _ }

instance (ε) : MonadExcept ε (Except ε) :=
{ throw := fun α => Except.error, catch := @Except.catch _ }

/-- Adapt a Monad stack, changing its top-most error Type.

    Note: This class can be seen as a simplification of the more "principled" definition
    ```
    class MonadExceptFunctor (ε ε' : outParam (Type u)) (n n' : Type u → Type u) :=
    (map {} {α : Type u} : (∀ {m : Type u → Type u} [Monad m], ExceptT ε m α → ExceptT ε' m α) → n α → n' α)
    ```
-/
class MonadExceptAdapter (ε ε' : outParam (Type u)) (m m' : Type u → Type v) :=
(adaptExcept {} {α : Type u} : (ε → ε') → m α → m' α)
export MonadExceptAdapter (adaptExcept)

section
variables {ε ε' : Type u} {m m' : Type u → Type v}

instance monadExceptAdapterTrans {n n' : Type u → Type v} [MonadFunctor m m' n n'] [MonadExceptAdapter ε ε' m m'] : MonadExceptAdapter ε ε' n n' :=
⟨fun α f => monadMap (fun α => (adaptExcept f : m α → m' α))⟩

instance [Monad m] : MonadExceptAdapter ε ε' (ExceptT ε m) (ExceptT ε' m) :=
⟨fun α => ExceptT.adapt⟩
end

instance (ε m out) [MonadRun out m] : MonadRun (fun α => out (Except ε α)) (ExceptT ε m) :=
⟨fun α => run⟩

-- useful for implicit failures in do-notation
instance (m : Type → Type) [Monad m] : MonadFail (ExceptT String m) :=
⟨fun _ => throw⟩
