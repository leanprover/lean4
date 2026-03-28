/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone, Leonardo de Moura, Mario Carneiro
-/
module

prelude
public import Init.Control.State

namespace Lake

/--
`EResult ε σ α` is equivalent to `Except ε α × σ`, but using a single
combined inductive yields a more efficient data representation.

This is a universe-polymorphic version of `EStateM.Result`.
-/
public inductive EResult (ε : Type u) (σ : Type v) (α : Type w) : Type max u v w
/-- A success value of type `α`, and a new state `σ`. -/
| ok    : α → σ → EResult ε σ α
/-- A failure value of type `ε`, and a new state `σ`. -/
| error : ε → σ → EResult ε σ α

namespace EResult

public instance [Inhabited α] [Inhabited σ] : Inhabited (EResult ε σ α) where
  default := EResult.ok default default

public instance [Inhabited ε] [Inhabited σ] : Inhabited (EResult ε σ α) where
  default := EResult.error default default

/-- Extract the state `σ` from a `EResult ε σ α`. -/
@[inline] public def state : EResult ε σ α → σ
| .ok _ s => s
| .error _ s => s

@[inline] public def modifyState (f : σ → σ') : EResult ε σ α → EResult ε σ' α
| .ok a s => .ok a (f s)
| .error e s => .error e (f s)

@[inline] public def setState (s : σ') (r : EResult ε σ α) : EResult ε σ' α :=
  r.modifyState fun _ => s

/-- Convert a `EResult ε σ α` into `Except ε α × σ`. -/
@[inline] public def toProd : EResult ε σ α → Except ε α × σ
| .ok a s => (.ok a, s)
| .error e s => (.error e, s)

/-- Convert an `EResult ε σ α` into `Option α × σ`, discarding the exception contents. -/
@[inline] public def toProd? : EResult ε σ α → Option α × σ
| .ok a s => (some a, s)
| .error _ s => (none, s)

/-- Extract the result `α` from a `EResult ε σ α`. -/
@[inline] public def result? : EResult ε σ α → Option α
| .ok a _ => some a
| _ => none

/-- Extract the error `ε` from a `EResult ε σ α`. -/
@[inline] public def error? : EResult ε σ α → Option ε
| .error e _ => some e
| _ => none

/-- Convert an `EResult ε σ α` into `Except ε α`, discarding its state. -/
@[inline] public def toExcept : EResult ε σ α → Except ε α
| .ok a _ => .ok a
| .error e _ => .error e

@[always_inline, inline]
public protected def map (f : α → β) : EResult ε σ α → EResult ε σ β
| .ok a s => .ok (f a) s
| .error e s => .error e s

public instance : Functor (EResult ε σ) where
  map := EResult.map

public def toEStateMResult : EResult ε σ α → EStateM.Result ε σ α
| .ok a s => .ok a s
| .error e s => .error e s

public def ofEStateMResult : EStateM.Result ε σ α → EResult ε σ α
| .ok a s => .ok a s
| .error e s => .error e s

end EResult

/--
`EStateT ε σ m` is a combined error and state monad transformer,
equivalent to `ExceptT ε (StateT σ m)` but more efficient.
-/
@[expose] public def EStateT (ε : Type u) (σ : Type v) (m : Type max u v w → Type x) (α : Type w) :=
  σ → m (EResult ε σ α)

namespace EStateT
variable {ε ε' : Type u} {σ : Type v} {α β : Type w}

/-- Construct an `EStateT` from its functional representation. -/
@[always_inline, inline]
public def mk (x : σ → m (EResult ε σ α)) : EStateT ε σ m α :=
  x

instance [Inhabited ε] [Pure m] : Inhabited (EStateT ε σ m α) where
  default := fun s => pure (EResult.error default s)

/-- Execute an `EStateT` on initial state `init` to get an `EResult` result. -/
@[always_inline, inline]
public def run (init : σ) (self : EStateT ε σ m α) : m (EResult ε σ α) :=
  self init

/--
Execute an `EStateT` on initial state `init`
to get an `Except` result, discarding the final state.
-/
@[always_inline, inline]
public def run' {σ : Type max u w} [Functor m] (init : σ) (x : EStateT ε σ m α) : m (Except ε α) :=
  EResult.toExcept <$> x init

/-- Convert an `EStateT` to a `StateT`, returning an `Except` result. -/
@[inline] public def toStateT {ε σ α : Type u} [Functor m] (x : EStateT ε σ m α) : StateT σ m (Except ε α) :=
  fun s => EResult.toProd <$> x s

/-- Convert an `EStateT` to a `StateT`, returning an `Option` result. -/
@[inline] public def toStateT? {ε σ α : Type u} [Functor m] (x : EStateT ε σ m α) : StateT σ m (Option α) :=
  fun s => EResult.toProd? <$> x s

/--
Execute an `EStateT` on initial state `init`
to get an `Option` result, discarding the exception contents.
-/
@[always_inline, inline]
public def run? {ε : Type max v w} [Functor m]  (init : σ) (x : EStateT ε σ m α) : m (Option α × σ) :=
  EResult.toProd? <$> x init

/--
Execute an `EStateT` on initial state `init` to get an `Option` result,
discarding the final state.
-/
@[always_inline, inline]
public def run?' {ε σ α : Type u} [Functor m] (init : σ) (x : EStateT ε σ m α) : m (Option α) :=
  EResult.result? <$> x init

@[inline] public def catchExceptions {ε σ α : Type u}
  [Monad m] (x : EStateT ε σ m α) (h : ε → StateT σ m α)
: StateT σ m α := fun s => do
  match (← x s) with
  | .ok a s => return (a, s)
  | .error e s => StateT.run (h e) s

/-- Lift the `m` monad into the `EStateT ε σ m` monad transformer. -/
@[always_inline, inline]
public def lift {ε σ α : Type u} [Monad m] (x : m α) : EStateT ε σ m α := fun s => do
  let a ← x; pure (.ok a s)

public instance {ε σ : Type u} [Monad m] : MonadLift m (EStateT ε σ m) := ⟨EStateT.lift⟩

/-- The `pure` operation of the `EStateT` monad transformer. -/
@[always_inline, inline]
public protected def pure [Pure m] (a : α) : EStateT ε σ m α := fun s =>
  pure <| .ok a s

public instance [Pure m] : Pure (EStateT ε σ m) where
  pure := EStateT.pure

/-- The `map` operation of the `EStateT` monad transformer. -/
@[always_inline, inline]
public protected def map [Functor m] (f : α → β) (x : EStateT ε σ m α) : EStateT ε σ m β := fun s =>
  x s |> Functor.map fun
  | .ok a s    => .ok (f a) s
  | .error e s => .error e s

public instance [Functor m] : Functor (EStateT ε σ m) where
  map := EStateT.map

/-- The `bind` operation of the `EStateT` monad transformer. -/
@[always_inline, inline]
public protected def bind [Monad m] (x : EStateT ε σ m α) (f : α → EStateT ε σ m β) : EStateT ε σ m β := fun s => do
  match (← x s) with
  | .ok a s    => f a s
  | .error e s => pure <| .error e s

/-- The `seqRight` operation of the `EStateT` monad transformer. -/
@[always_inline, inline]
public protected def seqRight [Monad m] (x : EStateT ε σ m α) (y : Unit → EStateT ε σ m β) : EStateT ε σ m β := fun s => do
  match (← x s) with
  | .ok _ s    => y () s
  | .error e s => pure <| .error e s

@[always_inline]
public instance [Monad m] : Monad (EStateT ε σ m) where
  bind     := EStateT.bind
  seqRight := EStateT.seqRight

/-- The `set` operation of the `EStateT` monad. -/
@[always_inline, inline]
public protected def set [Pure m] (s : σ) : EStateT ε σ m PUnit.{w+1} := fun _ =>
  pure <| .ok ⟨⟩ s

/-- The `get` operation of the `EStateT` monad. -/
@[always_inline, inline]
public protected def get [Pure m] : EStateT ε σ m σ := fun s =>
  pure <| .ok s s

/-- The `modifyGet` operation of the `EStateT` monad transformer. -/
@[always_inline, inline]
public protected def modifyGet [Pure m] (f : σ → Prod α σ) : EStateT ε σ m α := fun s =>
  match f s with | (a, s) => pure <| .ok a s

public instance [Pure m] : MonadStateOf σ (EStateT ε σ m) where
  set       := EStateT.set
  get       := EStateT.get
  modifyGet := EStateT.modifyGet

/-- The `throw` operation of the `EStateT` monad transformer. -/
@[always_inline, inline]
public protected def throw [Pure m] (e : ε) : EStateT ε σ m α := fun s =>
  pure <| .error e s

@[always_inline, inline]
public protected def tryCatch [Monad m] (x : EStateT ε σ m α) (handle : ε → EStateT ε σ m α) : EStateT ε σ m α := fun s => do
  match (← x s) with
  | .error e s => handle e s
  | ok         => pure ok

public instance [Monad m] : MonadExceptOf ε (EStateT ε σ m) where
  throw    := EStateT.throw
  tryCatch := EStateT.tryCatch

@[always_inline, inline]
public protected def orElse [Monad m] (x₁ : EStateT ε σ m α) (x₂ : Unit → EStateT ε σ m α) : EStateT ε σ m α := fun s => do
  match (← x₁ s) with
  | .error _ s => x₂ () s
  | ok         => pure ok

public instance [Monad m] : OrElse (EStateT ε σ m α) where
  orElse := EStateT.orElse

/-- Map the exception type of a `EStateT ε σ m α` by a function `f : ε → ε'`. -/
@[always_inline, inline]
public def adaptExcept [Functor m] (f : ε → ε') (x : EStateT ε σ m α) : EStateT ε' σ m α := fun s =>
  x s |> Functor.map fun
  | .error e s => .error (f e) s
  | .ok a s    => .ok a s

@[always_inline, inline]
public protected def tryFinally'
  [Monad m] (x : EStateT ε σ m α) (f : Option α → EStateT ε σ m β) : EStateT ε σ m (α × β)
:= fun s => do
  let r ← x s
  match r with
  | .ok a s => match (← f (some a) s) with
    | .ok b s => return .ok (a, b) s
    | .error e s => return .error e s
  | .error e₁ s => match (← f none s) with
    | .ok _ s => return .error e₁ s
    | .error e₂ s => return .error e₂ s

@[always_inline]
public instance [Monad m] : MonadFinally (EStateT ε σ m) where
  tryFinally' := EStateT.tryFinally'

/-- `EStateM` is analogous to `Lake.EStateT` with `m := Id`. -/
public def ofEStateM {ε σ α} (f : EStateM ε σ α) : Lake.EStateT ε σ Id α :=
  fun s => return .ofEStateMResult <| f s

/-- `Lake.EStateT` with `m := Id` and all the types in the same universe is analogous to `EStateM`. -/
public def toEStateM {ε σ α} (f : Lake.EStateT ε σ Id α) : EStateM ε σ α :=
  fun s => (f s).run.toEStateMResult

end EStateT
