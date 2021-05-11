/-
Copyright (c) 2020 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki
-/
import Init.System.IO

namespace IO

universe u v

/-- An async IO list is like a lazy list but instead of being *unevaluated* `Thunk`s,
lazy tails are `Task`s *being evaluated asynchronously*. A tail can signal the end
of computation (successful or due to a failure) with a terminating value of type `ε`. -/
inductive AsyncList (ε : Type u) (α : Type v) where
  | cons (hd : α) (tl : AsyncList ε α)
  | asyncTail (tl : Task $ Except ε $ AsyncList ε α)
  | nil

namespace AsyncList

instance : Inhabited (AsyncList ε α) := ⟨nil⟩

-- TODO(WN): tail-recursion without forcing sync?
partial def append : AsyncList ε α → AsyncList ε α → AsyncList ε α
  | cons hd tl, s => cons hd (append tl s)
  | asyncTail ttl, s => asyncTail (ttl.map $ Except.map (append · s))
  | nil, s => s

instance : Append (AsyncList ε α) := ⟨append⟩

def ofList : List α → AsyncList ε α :=
  List.foldr AsyncList.cons AsyncList.nil

instance : Coe (List α) (AsyncList ε α) := ⟨ofList⟩

private def coeErr {β} [Coe Error ε] (t : Task $ Except Error $ Except ε β) : Task (Except ε β) :=
  t.map $ fun
    | Except.ok v              => v
    | Except.error (e : Error) => Except.error (e : ε)

/-- Given a step computation `f` which takes the accumulator and either produces
another value or stops with a terminating value, produces an async stream of its
iterated applications. The initial value is *not* included. The computation can
throw IO exceptions, so to handle this the terminating value type must include
`IO.Error`.

For cooperatively cancelling an ongoing computation, we recommend referencing
a cancellation token in `f` and checking it when appropriate. -/
partial def unfoldAsync [Coe Error ε] (f : α → ExceptT ε IO α) (init : α)
: IO (AsyncList ε α) := do
  let rec step (a : α) : ExceptT ε IO (AsyncList ε α) := do
    let aNext ← f a
    let tNext ← coeErr <$> asTask (step aNext)
    return cons aNext $ asyncTail tNext

  let tInit ← coeErr <$> asTask (step init)
  asyncTail tInit

/-- The computed, synchronous list. If an async tail was present, returns also
its terminating value. -/
partial def getAll : AsyncList ε α → List α × Option ε
  | cons hd tl =>
    let ⟨l, e?⟩ := tl.getAll
    ⟨hd :: l, e?⟩
  | nil => ⟨[], none⟩
  | asyncTail tl =>
    match tl.get with
    | Except.ok tl => tl.getAll
    | Except.error e => ⟨[], some e⟩

/-- Spawns a `Task` waiting on the prefix of elements for which `p` is true. -/
partial def waitAll [Coe Error ε] (p : α → Bool := fun _ => true) : AsyncList ε α → IO (Task (List α × Option ε))
  | cons hd tl => do
    if p hd then
      let t ← tl.waitAll p
      t.map fun ⟨l, e?⟩ => ⟨hd :: l, e?⟩
    else
      return Task.pure ⟨[hd], none⟩
  | nil => return Task.pure ⟨[], none⟩
  | asyncTail tl => do
    let t : Task (Except IO.Error (List α × Option ε)) ← IO.bindTask tl fun
      | Except.ok tl => Task.map Except.ok <$> tl.waitAll p
      | Except.error e => return Task.pure <| Except.ok ⟨[], some e⟩
    t.map fun
      | Except.error e => ⟨[], some e⟩
      | Except.ok v => v

/-- Spawns a `Task` acting like `List.find?` but which will wait for tail evalution
when necessary to traverse the list. If the tail terminates before a matching element
is found, the task throws the terminating value. -/
partial def waitFind? (p : α → Bool) [Coe Error ε] : AsyncList ε α → IO (Task $ Except ε $ Option α)
  | nil => return Task.pure <| Except.ok none
  | cons hd tl => do
    if p hd then return Task.pure <| Except.ok <| some hd
    else tl.waitFind? p
  | asyncTail tl => do
    let t ← IO.bindTask tl fun
      | Except.ok tl => Task.map Except.ok <$> tl.waitFind? p
      | Except.error e => return Task.pure <| Except.ok <| Except.error e
    coeErr t

/-- Extends the `finishedPrefix` as far as possible. If computation was ongoing
and has finished, also returns the terminating value. -/
partial def updateFinishedPrefix : AsyncList ε α → IO (AsyncList ε α × Option ε)
  | cons hd tl => do
    let ⟨tl, e?⟩ ← tl.updateFinishedPrefix
    pure ⟨cons hd tl, e?⟩
  | nil => pure ⟨nil, none⟩
  | l@(asyncTail tl) => do
    if (← hasFinished tl) then
      match tl.get with
      | Except.ok tl => tl.updateFinishedPrefix
      | Except.error e => pure ⟨nil, some e⟩
    else pure ⟨l, none⟩

private partial def finishedPrefixAux : List α → AsyncList ε α → List α
  | acc, cons hd tl   => finishedPrefixAux (hd :: acc) tl
  | acc, nil          => acc
  | acc, asyncTail tl => acc

/-- The longest already-computed prefix of the list. -/
def finishedPrefix : AsyncList ε α → List α :=
  List.reverse ∘ (finishedPrefixAux [])

end AsyncList

end IO
