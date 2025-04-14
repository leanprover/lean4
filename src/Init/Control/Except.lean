/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jared Roesch, Sebastian Ullrich

The Except monad transformer.
-/
prelude
import Init.Control.Basic
import Init.Control.Id
import Init.Coe

namespace Except
variable {ε : Type u}

/--
A successful computation in the `Except ε` monad: `a` is returned, and no exception is thrown.
-/
@[always_inline, inline]
protected def pure (a : α) : Except ε α :=
  Except.ok a

/--
Transforms a successful result with a function, doing nothing when an exception is thrown.

Examples:
 * `(pure 2 : Except String Nat).map toString = pure 2`
 * `(throw "Error" : Except String Nat).map toString = throw "Error"`
-/
@[always_inline, inline]
protected def map (f : α → β) : Except ε α → Except ε β
  | Except.error err => Except.error err
  | Except.ok v => Except.ok <| f v

@[simp] theorem map_id : Except.map (ε := ε) (α := α) (β := α) id = id := by
  apply funext
  intro e
  simp [Except.map]; cases e <;> rfl

/--
Transforms exceptions with a function, doing nothing on successful results.

Examples:
 * `(pure 2 : Except String Nat).mapError (·.length) = pure 2`
 * `(throw "Error" : Except String Nat).mapError (·.length) = throw 5`
-/
@[always_inline, inline]
protected def mapError (f : ε → ε') : Except ε α → Except ε' α
  | Except.error err => Except.error <| f err
  | Except.ok v      => Except.ok v

/--
Sequences two operations that may throw exceptions, allowing the second to depend on the value
returned by the first.

If the first operation throws an exception, then it is the result of the computation. If the first
succeeds but the second throws an exception, then that exception is the result. If both succeed,
then the result is the result of the second computation.

This is the implementation of the `>>=` operator for `Except ε`.
-/
@[always_inline, inline]
protected def bind (ma : Except ε α) (f : α → Except ε β) : Except ε β :=
  match ma with
  | Except.error err => Except.error err
  | Except.ok v      => f v

/-- Returns `true` if the value is `Except.ok`, `false` otherwise. -/
@[always_inline, inline]
protected def toBool : Except ε α → Bool
  | Except.ok _    => true
  | Except.error _ => false

@[inherit_doc Except.toBool]
abbrev isOk : Except ε α → Bool := Except.toBool

/--
Returns `none` if an exception was thrown, or `some` around the value on success.

Examples:
 * `(pure 10 : Except String Nat).toOption = some 10`
 * `(throw "Failure" : Except String Nat).toOption = none`
-/
@[always_inline, inline]
protected def toOption : Except ε α → Option α
  | Except.ok a    => some a
  | Except.error _ => none

/--
Handles exceptions thrown in the `Except ε` monad.

If `ma` is successful, its result is returned. If it throws an exception, then `handle` is invoked
on the exception's value.

Examples:
 * `(pure 2 : Except String Nat).tryCatch (pure ·.length) = pure 2`
 * `(throw "Error" : Except String Nat).tryCatch (pure ·.length) = pure 5`
 * `(throw "Error" : Except String Nat).tryCatch (fun x => throw ("E: " ++ x)) = throw "E: Error"`
-/
@[always_inline, inline]
protected def tryCatch (ma : Except ε α) (handle : ε → Except ε α) : Except ε α :=
  match ma with
  | Except.ok a    => Except.ok a
  | Except.error e => handle e

/--
Recovers from exceptions thrown in the `Except ε` monad. Typically used via the `<|>` operator.

`Except.tryCatch` is a related operator that allows the recovery procedure to depend on _which_
exception was thrown.
-/
def orElseLazy (x : Except ε α) (y : Unit → Except ε α) : Except ε α :=
  match x with
  | Except.ok a    => Except.ok a
  | Except.error _ => y ()

@[always_inline]
instance : Monad (Except ε) where
  pure := Except.pure
  bind := Except.bind
  map  := Except.map

end Except

/--
Adds exceptions of type `ε` to a monad `m`.
-/
def ExceptT (ε : Type u) (m : Type u → Type v) (α : Type u) : Type v :=
  m (Except ε α)

/--
Use a monadic action that may return an exception's value as an action in the transformed monad that
may throw the corresponding exception.

This is the inverse of `ExceptT.run`.
-/
@[always_inline, inline]
def ExceptT.mk {ε : Type u} {m : Type u → Type v} {α : Type u} (x : m (Except ε α)) : ExceptT ε m α := x

/--
Use a monadic action that may throw an exception as an action that may return an exception's value.

This is the inverse of `ExceptT.mk`.
-/
@[always_inline, inline]
def ExceptT.run {ε : Type u} {m : Type u → Type v} {α : Type u} (x : ExceptT ε m α) : m (Except ε α) := x

namespace ExceptT

variable {ε : Type u} {m : Type u → Type v} [Monad m]

/--
Returns the value `a` without throwing exceptions or having any other effect.
-/
@[always_inline, inline]
protected def pure {α : Type u} (a : α) : ExceptT ε m α :=
  ExceptT.mk <| pure (Except.ok a)

/--
Handles exceptions thrown by an action that can have no effects _other_ than throwing exceptions.
-/
@[always_inline, inline]
protected def bindCont {α β : Type u} (f : α → ExceptT ε m β) : Except ε α → m (Except ε β)
  | Except.ok a    => f a
  | Except.error e => pure (Except.error e)

/--
Sequences two actions that may throw exceptions. Typically used via `do`-notation or the `>>=`
operator.
-/
@[always_inline, inline]
protected def bind {α β : Type u} (ma : ExceptT ε m α) (f : α → ExceptT ε m β) : ExceptT ε m β :=
  ExceptT.mk <| ma >>= ExceptT.bindCont f

/--
Transforms a successful computation's value using `f`. Typically used via the `<$>` operator.
-/
@[always_inline, inline]
protected def map {α β : Type u} (f : α → β) (x : ExceptT ε m α) : ExceptT ε m β :=
  ExceptT.mk <| x >>= fun a => match a with
    | (Except.ok a)    => pure <| Except.ok (f a)
    | (Except.error e) => pure <| Except.error e

/--
Runs a computation from an underlying monad in the transformed monad with exceptions.
-/
@[always_inline, inline]
protected def lift {α : Type u} (t : m α) : ExceptT ε m α :=
  ExceptT.mk <| Except.ok <$> t

@[always_inline]
instance : MonadLift (Except ε) (ExceptT ε m) := ⟨fun e => ExceptT.mk <| pure e⟩
instance : MonadLift m (ExceptT ε m) := ⟨ExceptT.lift⟩

/--
Handles exceptions produced in the `ExceptT ε` transformer.
-/
@[always_inline, inline]
protected def tryCatch {α : Type u} (ma : ExceptT ε m α) (handle : ε → ExceptT ε m α) : ExceptT ε m α :=
  ExceptT.mk <| ma >>= fun res => match res with
   | Except.ok a    => pure (Except.ok a)
   | Except.error e => (handle e)

instance : MonadFunctor m (ExceptT ε m) := ⟨fun f x => f x⟩

@[always_inline]
instance : Monad (ExceptT ε m) where
  pure := ExceptT.pure
  bind := ExceptT.bind
  map  := ExceptT.map

/--
Transforms exceptions using the function `f`.

This is the `ExceptT` version of `Except.mapError`.
-/
@[always_inline, inline]
protected def adapt {ε' α : Type u} (f : ε → ε') : ExceptT ε m α → ExceptT ε' m α := fun x =>
  ExceptT.mk <| Except.mapError f <$> x

end ExceptT

@[always_inline]
instance (m : Type u → Type v) (ε₁ : Type u) (ε₂ : Type u) [MonadExceptOf ε₁ m] : MonadExceptOf ε₁ (ExceptT ε₂ m) where
  throw e := ExceptT.mk <| throwThe ε₁ e
  tryCatch x handle := ExceptT.mk <| tryCatchThe ε₁ x handle

@[always_inline]
instance (m : Type u → Type v) (ε : Type u) [Monad m] : MonadExceptOf ε (ExceptT ε m) where
  throw e := ExceptT.mk <| pure (Except.error e)
  tryCatch := ExceptT.tryCatch

instance [Monad m] [Inhabited ε] : Inhabited (ExceptT ε m α) where
  default := throw default

instance (ε) : MonadExceptOf ε (Except ε) where
  throw    := Except.error
  tryCatch := Except.tryCatch

namespace MonadExcept
variable {ε : Type u} {m : Type v → Type w}

/--
An alternative unconditional error recovery operator that allows callers to specify which exception
to throw in cases where both operations throw exceptions.

By default, the first is thrown, because the `<|>` operator throws the second.
-/
@[always_inline, inline]
def orelse' [MonadExcept ε m] {α : Type v} (t₁ t₂ : m α) (useFirstEx := true) : m α :=
  tryCatch t₁ fun e₁ => tryCatch t₂ fun e₂ => throw (if useFirstEx then e₁ else e₂)

end MonadExcept

@[always_inline, inline]
def observing {ε α : Type u} {m : Type u → Type v} [Monad m] [MonadExcept ε m] (x : m α) : m (Except ε α) :=
  tryCatch (do let a ← x; pure (Except.ok a)) (fun ex => pure (Except.error ex))

def liftExcept [MonadExceptOf ε m] [Pure m] : Except ε α → m α
  | Except.ok a    => pure a
  | Except.error e => throw e

instance (ε : Type u) (m : Type u → Type v) [Monad m] : MonadControl m (ExceptT ε m) where
  stM        := Except ε
  liftWith f := liftM <| f fun x => x.run
  restoreM x := x

/--
Monads that provide the ability to ensure an action happens, regardless of exceptions or other
failures.

`MonadFinally.tryFinally'` is used to desugar `try ... finally ...` syntax.
-/
class MonadFinally (m : Type u → Type v) where
  /--
  Runs an action, ensuring that some other action always happens afterward.

  More specifically, `tryFinally' x f` runs `x` and then the “finally” computation `f`. If `x`
  succeeds with some value `a : α`, `f (some a)` is returned. If `x` fails for `m`'s definition of
  failure, `f none` is returned.

  `tryFinally'` can be thought of as performing the same role as a `finally` block in an imperative
  programming language.
  -/
  tryFinally' {α β} : (x : m α) → (f : Option α → m β) → m (α × β)

export MonadFinally (tryFinally')

/-- Execute `x` and then execute `finalizer` even if `x` threw an exception -/
@[always_inline, inline]
def tryFinally {m : Type u → Type v} {α β : Type u} [MonadFinally m] [Functor m] (x : m α) (finalizer : m β) : m α :=
  let y := tryFinally' x (fun _ => finalizer)
  (·.1) <$> y

@[always_inline]
instance Id.finally : MonadFinally Id where
  tryFinally' := fun x h =>
   let a := x
   let b := h (some x)
   pure (a, b)

@[always_inline]
instance ExceptT.finally {m : Type u → Type v} {ε : Type u} [MonadFinally m] [Monad m] : MonadFinally (ExceptT ε m) where
  tryFinally' := fun x h => ExceptT.mk do
    let r ← tryFinally' x fun e? => match e? with
        | some (.ok a) => h (some a)
        | _            => h none
    match r with
    | (.ok a,    .ok b)    => pure (.ok (a, b))
    | (_,        .error e) => pure (.error e)  -- second error has precedence
    | (.error e, _)        => pure (.error e)
