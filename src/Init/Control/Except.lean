/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jared Roesch, Sebastian Ullrich

The Except monad transformer.
-/
prelude
import Init.Data.ToString.Basic
import Init.Control.Alternative
import Init.Control.MonadControl
import Init.Control.Id
import Init.Control.MonadFunctor

universes u v w u'

inductive Except (ε : Type u) (α : Type v)
| error : ε → Except
| ok    : α → Except

attribute [unbox] Except

instance {ε : Type u} {α : Type v} [Inhabited ε] : Inhabited (Except ε α) :=
⟨Except.error (arbitrary ε)⟩

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

@[inline] protected def tryCatch {α : Type u} (ma : Except ε α) (handle : ε → Except ε α) : Except ε α :=
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

instance exceptTOfExcept : MonadLift (Except ε) (ExceptT ε m) :=
⟨fun α e => ExceptT.mk $ pure e⟩

instance : MonadLift m (ExceptT ε m) :=
⟨@ExceptT.lift _ _ _⟩

@[inline] protected def tryCatch {α : Type u} (ma : ExceptT ε m α) (handle : ε → ExceptT ε m α) : ExceptT ε m α :=
ExceptT.mk $ ma >>= fun res => match res with
 | Except.ok a    => pure (Except.ok a)
 | Except.error e => (handle e)

instance : MonadFunctor m (ExceptT ε m) :=
⟨fun _ f x => f x⟩

instance : Monad (ExceptT ε m) :=
{ pure := @ExceptT.pure _ _ _, bind := @ExceptT.bind _ _ _, map := @ExceptT.map _ _ _ }

@[inline] protected def adapt {ε' α : Type u} (f : ε → ε') : ExceptT ε m α → ExceptT ε' m α :=
fun x => ExceptT.mk $ Except.mapError f <$> x
end ExceptT

/-- An implementation of [MonadError](https://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-Except.html#t:MonadError) -/
class MonadExceptOf (ε : Type u) (m : Type v → Type w) :=
(throw {α : Type v} : ε → m α)
(tryCatch {α : Type v} : m α → (ε → m α) → m α)

abbrev throwThe (ε : Type u) {m : Type v → Type w} [MonadExceptOf ε m] {α : Type v} (e : ε) : m α :=
MonadExceptOf.throw e

abbrev tryCatchThe (ε : Type u) {m : Type v → Type w} [MonadExceptOf ε m] {α : Type v} (x : m α) (handle : ε → m α) : m α :=
MonadExceptOf.tryCatch x handle

instance ExceptT.monadExceptParent (m : Type u → Type v) (ε₁ : Type u) (ε₂ : Type u) [Monad m] [MonadExceptOf ε₁ m] : MonadExceptOf ε₁ (ExceptT ε₂ m) :=
{ throw    := fun α e        => ExceptT.mk $ throwThe ε₁ e,
  tryCatch := fun α x handle => ExceptT.mk $ tryCatchThe ε₁ x handle }

instance ExceptT.monadExceptSelf (m : Type u → Type v) (ε : Type u) [Monad m] : MonadExceptOf ε (ExceptT ε m) :=
{ throw := fun α e => ExceptT.mk $ pure (Except.error e),
  tryCatch := @ExceptT.tryCatch ε _ _ }

instance (ε) : MonadExceptOf ε (Except ε) :=
{ throw := fun α => Except.error,
  tryCatch := @Except.tryCatch _ }

/-- Similar to `MonadExceptOf`, but `ε` is an outParam for convenience -/
class MonadExcept (ε : outParam (Type u)) (m : Type v → Type w) :=
(throw {α : Type v} : ε → m α)
(tryCatch {α : Type v} : m α → (ε → m α) → m α)

export MonadExcept (throw tryCatch)

instance MonadExceptOf.isMonadExcept (ε : outParam (Type u)) (m : Type v → Type w) [MonadExceptOf ε m] : MonadExcept ε m :=
{ throw := fun _ e        => throwThe ε e,
  tryCatch := fun _ x handle => tryCatchThe ε x handle }

namespace MonadExcept
variables {ε : Type u} {m : Type v → Type w}

@[inline] protected def orelse [MonadExcept ε m] {α : Type v} (t₁ t₂ : m α) : m α :=
tryCatch t₁ $ fun _ => t₂

instance [MonadExcept ε m] {α : Type v} : HasOrelse (m α) :=
⟨MonadExcept.orelse⟩

/-- Alternative orelse operator that allows to select which exception should be used.
    The default is to use the first exception since the standard `orelse` uses the second. -/
@[inline] def orelse' [MonadExcept ε m] {α : Type v} (t₁ t₂ : m α) (useFirstEx := true) : m α :=
tryCatch t₁ $ fun e₁ => tryCatch t₂ $ fun e₂ => throw (if useFirstEx then e₁ else e₂)

end MonadExcept

@[inline] def observing {ε α : Type u} {m : Type u → Type v} [Monad m] [MonadExcept ε m] (x : m α) : m (Except ε α) :=
tryCatch (do a ← x; pure (Except.ok a)) (fun ex => pure (Except.error ex))

instance ExceptT.monadControl (ε : Type u) (m : Type u → Type v) [Monad m] : MonadControl m (ExceptT ε m) := {
  stM      := fun α   => Except ε α,
  liftWith := fun α f => liftM $ f fun β x => x.run,
  restoreM := fun α x => x,
}

class MonadFinally (m : Type u → Type v) :=
(tryFinally' {α β} : m α → (Option α → m β) → m (α × β))

export MonadFinally (tryFinally')

/-- Execute `x` and then execute `finalizer` even if `x` threw an exception -/
@[inline] abbrev tryFinally {m : Type u → Type v} {α β : Type u} [MonadFinally m] [Functor m] (x : m α) (finalizer : m β) : m α := do
Prod.fst <$> tryFinally' x (fun _ => finalizer)

instance Id.finally : MonadFinally Id :=
{ tryFinally' := fun α β x h =>
   let a := x;
   let b := h (some x);
   pure (a, b) }

instance ExceptT.finally {m : Type u → Type v} {ε : Type u} [MonadFinally m] [Monad m] : MonadFinally (ExceptT ε m) :=
{ tryFinally' := fun α β x h => ExceptT.mk do
    r ← tryFinally' x (fun e? => match e? with
        | some (Except.ok a) => h (some a)
        | _                  => h none);
    match r with
    | (Except.ok a,    Except.ok b)    => pure (Except.ok (a, b))
    | (_,              Except.error e) => pure (Except.error e)  -- second error has precedence
    | (Except.error e, _)              => pure (Except.error e)  }
