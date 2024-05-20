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

@[always_inline, inline]
protected def pure (a : α) : Except ε α :=
  Except.ok a

@[always_inline, inline]
protected def map (f : α → β) : Except ε α → Except ε β
  | Except.error err => Except.error err
  | Except.ok v => Except.ok <| f v

@[simp] theorem map_id : Except.map (ε := ε) (α := α) (β := α) id = id := by
  apply funext
  intro e
  simp [Except.map]; cases e <;> rfl

@[always_inline, inline]
protected def mapError (f : ε → ε') : Except ε α → Except ε' α
  | Except.error err => Except.error <| f err
  | Except.ok v      => Except.ok v

@[always_inline, inline]
protected def bind (ma : Except ε α) (f : α → Except ε β) : Except ε β :=
  match ma with
  | Except.error err => Except.error err
  | Except.ok v      => f v

/-- Returns true if the value is `Except.ok`, false otherwise. -/
@[always_inline, inline]
protected def toBool : Except ε α → Bool
  | Except.ok _    => true
  | Except.error _ => false

abbrev isOk : Except ε α → Bool := Except.toBool

@[always_inline, inline]
protected def toOption : Except ε α → Option α
  | Except.ok a    => some a
  | Except.error _ => none

@[always_inline, inline]
protected def tryCatch (ma : Except ε α) (handle : ε → Except ε α) : Except ε α :=
  match ma with
  | Except.ok a    => Except.ok a
  | Except.error e => handle e

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

def ExceptT (ε : Type u) (m : Type u → Type v) (α : Type u) : Type v :=
  m (Except ε α)

@[always_inline, inline]
def ExceptT.mk {ε : Type u} {m : Type u → Type v} {α : Type u} (x : m (Except ε α)) : ExceptT ε m α := x

@[always_inline, inline]
def ExceptT.run {ε : Type u} {m : Type u → Type v} {α : Type u} (x : ExceptT ε m α) : m (Except ε α) := x

namespace ExceptT

variable {ε : Type u} {m : Type u → Type v} [Monad m]

@[always_inline, inline]
protected def pure {α : Type u} (a : α) : ExceptT ε m α :=
  ExceptT.mk <| pure (Except.ok a)

@[always_inline, inline]
protected def bindCont {α β : Type u} (f : α → ExceptT ε m β) : Except ε α → m (Except ε β)
  | Except.ok a    => f a
  | Except.error e => pure (Except.error e)

@[always_inline, inline]
protected def bind {α β : Type u} (ma : ExceptT ε m α) (f : α → ExceptT ε m β) : ExceptT ε m β :=
  ExceptT.mk <| ma >>= ExceptT.bindCont f

@[always_inline, inline]
protected def map {α β : Type u} (f : α → β) (x : ExceptT ε m α) : ExceptT ε m β :=
  ExceptT.mk <| x >>= fun a => match a with
    | (Except.ok a)    => pure <| Except.ok (f a)
    | (Except.error e) => pure <| Except.error e

@[always_inline, inline]
protected def lift {α : Type u} (t : m α) : ExceptT ε m α :=
  ExceptT.mk <| Except.ok <$> t

@[always_inline]
instance : MonadLift (Except ε) (ExceptT ε m) := ⟨fun e => ExceptT.mk <| pure e⟩
instance : MonadLift m (ExceptT ε m) := ⟨ExceptT.lift⟩

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

@[always_inline, inline]
protected def adapt {ε' α : Type u} (f : ε → ε') : ExceptT ε m α → ExceptT ε' m α := fun x =>
  ExceptT.mk <| Except.mapError f <$> x

end ExceptT

@[always_inline]
instance (m : Type u → Type v) (ε₁ : Type u) (ε₂ : Type u) [Monad m] [MonadExceptOf ε₁ m] : MonadExceptOf ε₁ (ExceptT ε₂ m) where
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

/-- Alternative orelse operator that allows to select which exception should be used.
    The default is to use the first exception since the standard `orelse` uses the second. -/
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

class MonadFinally (m : Type u → Type v) where
  /-- `tryFinally' x f` runs `x` and then the "finally" computation `f`.
  When `x` succeeds with `a : α`, `f (some a)` is returned. If `x` fails
  for `m`'s definition of failure, `f none` is returned. Hence `tryFinally'`
  can be thought of as performing the same role as a `finally` block in
  an imperative programming language. -/
  tryFinally' {α β} : m α → (Option α → m β) → m (α × β)

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
