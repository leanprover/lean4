/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone, Leonardo de Moura, Mario Carneiro
-/

namespace Lake

/--
`EResult ε σ α` is equivalent to `Except ε α × σ`, but using a single
combined inductive yields a more efficient data representation.
-/
inductive EResult (ε : Type u) (σ : Type v) (α : Type w) : Type max u v w
/-- A success value of type `α`, and a new state `σ`. -/
| ok    : α → σ → EResult ε σ α
/-- A failure value of type `ε`, and a new state `σ`. -/
| error : ε → σ → EResult ε σ α

instance [Inhabited α] [Inhabited σ] : Inhabited (EResult ε σ α) where
  default := EResult.ok default default

instance [Inhabited ε] [Inhabited σ] : Inhabited (EResult ε σ α) where
  default := EResult.error default default

/-- Extract the state `σ` from a `EResult ε σ α`. -/
@[inline] def EResult.state : EResult ε σ α → σ
| .ok _ s => s
| .error _ s => s

@[inline] def EResult.setState (s : σ') : EResult ε σ α → EResult ε σ' α
| .ok a _ => .ok a s
| .error e _ => .error e s

/-- Extract the result `α` from a `EResult ε σ α`. -/
@[inline] def EResult.result? : EResult ε σ α → Option α
| .ok a _ => some a
| _ => none

/-- Extract the error `ε` from a `EResult ε σ α`. -/
@[inline] def EResult.error? : EResult ε σ α → Option ε
| .error e _ => some e
| _ => none

/-- Convert an `EResult ε σ α` into `Except ε α`, discarding its state. -/
@[inline] def EResult.toExcept : EResult ε σ α → Except ε α
| .ok a _ => .ok a
| .error e _ => .error e

@[always_inline, inline]
protected def EResult.map (f : α → β) : EResult ε σ α → EResult ε σ β
| .ok a s => .ok (f a) s
| .error e s => .error e s

instance : Functor (EResult ε σ) where
  map := EResult.map

/--
`EStateT ε σ m` is a combined error and state monad transformer,
equivalent to `ExceptT ε (StateT σ m)` but more efficient.
-/
def EStateT (ε : Type u) (σ : Type v) (m : Type max u v w → Type x) (α : Type w) :=
  σ → m (EResult ε σ α)

namespace EStateT

instance [Inhabited ε] [Pure m] : Inhabited (EStateT ε σ m α) where
  default := fun s => pure (EResult.error default s)

/-- Lift the `m` monad into the `EStateT ε σ m` monad transformer. -/
@[always_inline, inline]
protected def lift {ε σ α : Type u} [Monad m] (x : m α) : EStateT ε σ m α := fun s => do
  let a ← x; pure (.ok a s)

instance [Monad m] : MonadLift m (EStateT ε σ m) := ⟨EStateT.lift⟩

variable {ε ε' : Type u} {σ : Type v} {α β : Type w}

/-- Execute an `EStateT` on initial state `s` to get an `EResult` result. -/
@[always_inline, inline]
def run (init : σ) (self : EStateT ε σ m α) : m (EResult ε σ α) :=
  self init

/-- Execute an `EStateT` on initial state `s` to get an `Except` result. -/
@[always_inline, inline]
def run' {σ : Type max u w} [Functor m] (init : σ) (self : EStateT ε σ m α) : m (Except ε α) :=
  EResult.toExcept <$> self init

/-- The `pure` operation of the `EStateT` monad transformer. -/
@[always_inline, inline]
protected def pure [Pure m] (a : α) : EStateT ε σ m α := fun s =>
  pure <| .ok a s

instance [Pure m] : Pure (EStateT ε σ m) where
  pure := EStateT.pure

/-- The `map` operation of the `EStateT` monad transformer. -/
@[always_inline, inline]
protected def map [Functor m] (f : α → β) (x : EStateT ε σ m α) : EStateT ε σ m β := fun s =>
  x s |> Functor.map fun
  | .ok a s    => .ok (f a) s
  | .error e s => .error e s

instance [Functor m] : Functor (EStateT ε σ m) where
  map := EStateT.map

/-- The `bind` operation of the `EStateT` monad transformer. -/
@[always_inline, inline]
protected def bind [Monad m] (x : EStateT ε σ m α) (f : α → EStateT ε σ m β) : EStateT ε σ m β := fun s => do
  match (← x s) with
  | .ok a s    => f a s
  | .error e s => pure <| .error e s

/-- The `seqRight` operation of the `EStateT` monad transformer. -/
@[always_inline, inline]
protected def seqRight [Monad m] (x : EStateT ε σ m α) (y : Unit → EStateT ε σ m β) : EStateT ε σ m β := fun s => do
  match (← x s) with
  | .ok _ s    => y () s
  | .error e s => pure <| .error e s

@[always_inline]
instance [Monad m] : Monad (EStateT ε σ m) where
  bind     := EStateT.bind
  seqRight := EStateT.seqRight

/-- The `set` operation of the `EStateT` monad. -/
@[always_inline, inline]
protected def set [Pure m] (s : σ) : EStateT ε σ m PUnit.{w+1} := fun _ =>
  pure <| .ok ⟨⟩ s

/-- The `get` operation of the `EStateT` monad. -/
@[always_inline, inline]
protected def get [Pure m]  : EStateT ε σ m σ := fun s =>
  pure <| .ok s s

/-- The `modifyGet` operation of the `EStateT` monad transformer. -/
@[always_inline, inline]
protected def modifyGet [Pure m] (f : σ → Prod α σ) : EStateT ε σ m α := fun s =>
  match f s with | (a, s) => pure <| .ok a s

instance [Pure m] : MonadStateOf σ (EStateT ε σ m) where
  set       := EStateT.set
  get       := EStateT.get
  modifyGet := EStateT.modifyGet

/-- The `throw` operation of the `EStateT` monad transformer. -/
@[always_inline, inline]
protected def throw [Pure m] (e : ε) : EStateT ε σ m α := fun s =>
  pure <| .error e s

@[always_inline, inline]
protected def tryCatch [Monad m] (x : EStateT ε σ m α) (handle : ε → EStateT ε σ m α) : EStateT ε σ m α := fun s => do
  match (← x s) with
  | .error e s => handle e s
  | ok         => pure ok

instance [Monad m] : MonadExceptOf ε (EStateT ε σ m) where
  throw    := EStateT.throw
  tryCatch := EStateT.tryCatch

@[always_inline, inline]
protected def orElse [Monad m] (x₁ : EStateT ε σ m α) (x₂ : Unit → EStateT ε σ m α) : EStateT ε σ m α := fun s => do
  match (← x₁ s) with
  | .error _ s => x₂ () s
  | ok         => pure ok

instance [Monad m] : OrElse (EStateT ε σ m α) where
  orElse := EStateT.orElse

/-- Map the exception type of a `EStateT ε σ m α` by a function `f : ε → ε'`. -/
@[always_inline, inline]
def adaptExcept [Functor m] (f : ε → ε') (x : EStateT ε σ m α) : EStateT ε' σ m α := fun s =>
  x s |> Functor.map fun
  | .error e s => .error (f e) s
  | .ok a s    => .ok a s

@[always_inline]
instance [Monad m] : MonadFinally (EStateT ε σ m) where
  tryFinally' x h s := do
    let r ← x s
    match r with
    | .ok a s => match (← h (some a) s) with
      | .ok b s => return .ok (a, b) s
      | .error e s => return .error e s
    | .error e₁ s => match (← h none s) with
      | .ok _ s => return .error e₁ s
      | .error e₂ s => return .error e₂ s
