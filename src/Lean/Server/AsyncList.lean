/-
Copyright (c) 2020 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki
-/
import Init.System.IO

namespace IO

universes u v

/-- An async IO list is like a lazy list but instead of being *unevaluated* `Thunk`s,
lazy tails are `Task`s *being evaluated asynchronously*. A tail can signal the end
of computation (successful or due to a failure) with a terminating value of type `ε`. -/
inductive AsyncList (ε : Type u) (α : Type v) :=
  | cons (hd : α) (tl : AsyncList ε α)
  | asyncCons (hd : α) (tl : Task $ Except ε $ AsyncList ε α)
  | nil

namespace AsyncList

-- TODO(WN): IO doesn't like universes :(
variables {ε : Type} {α : Type}

instance asyncListInhabited : Inhabited (AsyncList ε α) := ⟨nil⟩

-- TODO(WN): tail-recursion without forcing sync?
partial def append : AsyncList ε α → AsyncList ε α → AsyncList ε α
  | cons hd tl, s => cons hd (append tl s)
  | asyncCons hd ttl, s => asyncCons hd (ttl.map $ Except.map (append · s))
  | nil, s => s

instance : Append (AsyncList ε α) := ⟨append⟩

def ofList : List α → AsyncList ε α :=
  List.foldr AsyncList.cons AsyncList.nil

instance : Coe (List α) (AsyncList ε α) := ⟨ofList⟩

/-- Given a step computation `f` which takes the accumulator and either produces
another value or stops with a terminating value, produces an async stream of its
iterated applications. The computation can throw IO exceptions, so to handle this
the terminating value type must include `IO.Error`.

Optionally, a specified computation can be ran on task cancellation.
An alternative for cooperative concurrency is to check this in `f`. -/
partial def unfoldAsync [Coe Error ε] (f : α → ExceptT ε IO α)
  (init : α) (onCanceled : Option (α → IO ε) := none)
: IO (AsyncList ε α) := do
  let coeErr (t : Task $ Except Error $ Except ε $ AsyncList ε α) : Task (Except ε $ AsyncList ε α) :=
    t.map $ fun
      | Except.ok v              => v
      | Except.error (e : Error) => Except.error (e : ε)

  let rec step (a : α) : ExceptT ε IO (AsyncList ε α) := do
    if onCanceled.isSome ∧ (← checkCanceled) then
      throw (← onCanceled.get! a)
    else
      let aNext ← f a
      let tNext ← coeErr <$> asTask (step aNext)
      return asyncCons aNext tNext

  let tInit ← coeErr <$> asTask (step init)
  asyncCons init tInit

/-- Waits for the entire computation to finish and returns the computed
list. If computation was ongoing, also returns the terminating value. -/
partial def waitAll : AsyncList ε α → List α × Option ε
  | cons hd tl =>
    let ⟨l, e?⟩ := tl.waitAll
    ⟨hd :: l, e?⟩
  | nil => ⟨[], none⟩
  | asyncCons hd tl =>
    match tl.get with
    | Except.ok tl =>
      let ⟨l, e?⟩ := tl.waitAll
      ⟨hd :: l, e?⟩
    | Except.error e => ⟨[hd], some e⟩

/-- Extends the `finishedPrefix` as far as possible. If computation was ongoing
and has finished, also returns the terminating value. -/
partial def updateFinishedPrefix : AsyncList ε α → IO (AsyncList ε α × Option ε)
  | cons hd tl => do
    let ⟨tl, e?⟩ ← tl.updateFinishedPrefix
    pure ⟨cons hd tl, e?⟩
  | nil => pure ⟨nil, none⟩
  | l@(asyncCons hd tl) => do
    if (← hasFinished tl) then
      match tl.get with
      | Except.ok tl =>
        let ⟨tl, e?⟩ ← tl.updateFinishedPrefix
        pure ⟨cons hd tl, e?⟩
      | Except.error e => pure ⟨cons hd nil, some e⟩
    else pure ⟨l, none⟩

private partial def finishedPrefixAux : List α → AsyncList ε α → List α
  | acc, cons hd tl      => finishedPrefixAux (hd :: acc) tl
  | acc, nil             => acc
  | acc, asyncCons hd tl => acc

/-- The longest already-computed prefix of the stream. -/
def finishedPrefix : AsyncList ε α → List α :=
  List.reverse ∘ (finishedPrefixAux [])

end AsyncList

end IO
