/-
Copyright (c) 2020 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki
-/
prelude
import Init.System.IO
import Init.System.Promise

namespace IO

universe u v

/-- An async IO list is like a lazy list but instead of being *unevaluated* `Thunk`s,
`delayed` suffixes are `Task`s *being evaluated asynchronously*. A delayed suffix can signal the end
of computation (successful or due to a failure) with a terminating value of type `ε`. -/
inductive AsyncList (ε : Type u) (α : Type v) where
  | cons (hd : α) (tl : AsyncList ε α)
  | delayed (tl : Task $ Except ε $ AsyncList ε α)
  | nil

namespace AsyncList

instance : Inhabited (AsyncList ε α) := ⟨nil⟩

-- TODO(WN): tail-recursion without forcing sync?
partial def append : AsyncList ε α → AsyncList ε α → AsyncList ε α
  | cons hd tl, s => cons hd (append tl s)
  | delayed ttl, s => delayed (ttl.map $ Except.map (append · s))
  | nil, s => s

instance : Append (AsyncList ε α) := ⟨append⟩

def ofList : List α → AsyncList ε α :=
  List.foldr AsyncList.cons AsyncList.nil

instance : Coe (List α) (AsyncList ε α) := ⟨ofList⟩

/-- A stateful step computation `f` is applied iteratively, forming an async
stream. The stream ends once `f` returns `none` for the first time.

For cooperatively cancelling an ongoing computation, we recommend referencing
a cancellation token in `f` and checking it when appropriate. -/
partial def unfoldAsync (f : StateT σ (EIO ε) $ Option α) (init : σ)
    : BaseIO (AsyncList ε α) := do
  let rec step (s : σ) : EIO ε (AsyncList ε α) := do
    let (aNext, sNext) ← f s
    match aNext with
      | none => return nil
      | some aNext => do
        let tNext ← EIO.asTask (step sNext)
        return cons aNext $ delayed tNext

  let tInit ← EIO.asTask (step init)
  return delayed tInit

/-- The computed, synchronous list. If an async tail was present, returns also
its terminating value. -/
partial def getAll : AsyncList ε α → List α × Option ε
  | cons hd tl =>
    let ⟨l, e?⟩ := tl.getAll
    ⟨hd :: l, e?⟩
  | nil => ⟨[], none⟩
  | delayed tl =>
    match tl.get with
    | Except.ok tl => tl.getAll
    | Except.error e => ⟨[], some e⟩

/-- Spawns a `Task` returning the prefix of elements up to (including) the first element for which `p` is true.
When `p` is not true of any element, it returns the entire list. -/
partial def waitUntil (p : α → Bool) : AsyncList ε α → Task (List α × Option ε)
  | cons hd tl =>
    if !p hd then
      (tl.waitUntil p).map fun ⟨l, e?⟩ => ⟨hd :: l, e?⟩
    else
      .pure ⟨[hd], none⟩
  | nil => .pure ⟨[], none⟩
  | delayed tl =>
    tl.bind fun
      | .ok tl   => tl.waitUntil p
      | .error e => .pure ⟨[], some e⟩

/-- Spawns a `Task` waiting on all elements. -/
def waitAll : AsyncList ε α → Task (List α × Option ε) :=
  waitUntil (fun _ => false)

/-- Spawns a `Task` acting like `List.find?` but which will wait for tail evaluation
when necessary to traverse the list. If the tail terminates before a matching element
is found, the task throws the terminating value. -/
partial def waitFind? (p : α → Bool) : AsyncList ε α → Task (Except ε (Option α))
  | nil => .pure <| .ok none
  | cons hd tl =>
    if p hd then .pure <| Except.ok <| some hd
    else tl.waitFind? p
  | delayed tl =>
    tl.bind fun
      | .ok tl   => tl.waitFind? p
      | .error e => .pure <| .error e

/--
Retrieve the already-computed prefix of the list. If computation has finished with an error, return it as well.
The returned boolean indicates whether the complete `AsyncList` was returned, or whether only a
proper prefix was returned.
-/
partial def getFinishedPrefix : AsyncList ε α → BaseIO (List α × Option ε × Bool)
  | cons hd tl => do
    let ⟨tl, e?, isComplete⟩ ← tl.getFinishedPrefix
    pure ⟨hd :: tl, e?, isComplete⟩
  | nil => pure ⟨[], none, true⟩
  | delayed tl => do
    if (← hasFinished tl) then
      match tl.get with
      | Except.ok tl => tl.getFinishedPrefix
      | Except.error e => pure ⟨[], some e, true⟩
    else pure ⟨[], none, false⟩

partial def getFinishedPrefixWithTimeout (xs : AsyncList ε α) (timeoutMs : UInt32)
    (cancelTk? : Option (Task Unit) := none) : BaseIO (List α × Option ε × Bool) := do
  let timeoutTask : Task (Unit ⊕ Except ε (AsyncList ε α)) ←
    if timeoutMs == 0 then
      pure <| Task.pure (Sum.inl ())
    else
      BaseIO.asTask (prio := .dedicated) do
        IO.sleep timeoutMs
        return .inl ()
  go timeoutTask xs
where
  go (timeoutTask : Task (Unit ⊕ Except ε (AsyncList ε α)))
      (xs : AsyncList ε α) : BaseIO (List α × Option ε × Bool) := do
    match xs with
    | cons hd tl =>
      let ⟨tl, e?, isComplete⟩ ← go timeoutTask tl
      return ⟨hd :: tl, e?, isComplete⟩
    | nil => return ⟨[], none, true⟩
    | delayed tl =>
      let tl := tl.map (sync := true) .inr
      let cancelTk? := do return (← cancelTk?).map (sync := true) .inl
      let tasks : { t : List _ // t.length > 0 } :=
        match cancelTk? with
        | none => ⟨[tl, timeoutTask], by exact Nat.zero_lt_succ _⟩
        | some cancelTk => ⟨[cancelTk, tl, timeoutTask], by exact Nat.zero_lt_succ _⟩
      let r ← IO.waitAny tasks.val (h := tasks.property)
      match r with
      | .inl _ => return ⟨[], none, false⟩ -- Timeout or cancellation - stop waiting
      | .inr (.ok tl) => go timeoutTask tl
      | .inr (.error e) => return ⟨[], some e, true⟩

partial def getFinishedPrefixWithConsistentLatency (xs : AsyncList ε α) (latencyMs : UInt32)
    (cancelTk? : Option (Task Unit) := none) : BaseIO (List α × Option ε × Bool) := do
  let timestamp ← IO.monoMsNow
  let r ← xs.getFinishedPrefixWithTimeout latencyMs cancelTk?
  let passedTimeMs := (← IO.monoMsNow) - timestamp
  let remainingLatencyMs := (latencyMs.toNat - passedTimeMs).toUInt32
  sleepWithCancellation remainingLatencyMs
  return r
where
  sleepWithCancellation (sleepDurationMs : UInt32) : BaseIO Unit := do
    if sleepDurationMs == 0 then
      return
    let some cancelTk := cancelTk?
      | IO.sleep sleepDurationMs
        return
    if ← IO.hasFinished cancelTk then
      return
    let sleepTask ← BaseIO.asTask (prio := .dedicated) do
      IO.sleep sleepDurationMs
    IO.waitAny [sleepTask, cancelTk]


def waitHead? (as : AsyncList ε α) : Task (Except ε (Option α)) :=
  as.waitFind? fun _ => true

/-- Cancels all tasks in the list. -/
partial def cancel : AsyncList ε α → BaseIO Unit
  | cons _ tl => tl.cancel
  | nil => pure ()
  | delayed tl => do
    -- mind the order: if we asked the task whether it is still running
    -- *before* cancelling it, it could be the case that it finished
    -- just in between and has enqueued a dependent task that we would
    -- miss (recall that cancellation is inherited by dependent tasks)
    IO.cancel tl
    if (← hasFinished tl) then
      if let .ok t := tl.get then
        t.cancel

end AsyncList

end IO
