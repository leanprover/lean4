/-
Copyright (c) 2020 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki
-/
prelude
import Lean.Server.ServerTask
import Init.System.Promise

namespace IO

universe u v

/-- An async IO list is like a lazy list but instead of being *unevaluated* `Thunk`s,
`delayed` suffixes are `Task`s *being evaluated asynchronously*. A delayed suffix can signal the end
of computation (successful or due to a failure) with a terminating value of type `ε`. -/
inductive AsyncList (ε : Type u) (α : Type v) where
  | cons (hd : α) (tl : AsyncList ε α)
  | delayed (tl : Lean.Server.ServerTask $ Except ε $ AsyncList ε α)
  | nil

namespace AsyncList

open Lean.Server

instance : Inhabited (AsyncList ε α) := ⟨nil⟩

def ofList : List α → AsyncList ε α :=
  List.foldr AsyncList.cons AsyncList.nil

instance : Coe (List α) (AsyncList ε α) := ⟨ofList⟩

/-- Spawns a `Task` returning the prefix of elements up to (including) the first element for which `p` is true.
When `p` is not true of any element, it returns the entire list. -/
partial def waitUntil (p : α → Bool) : AsyncList ε α → ServerTask (List α × Option ε)
  | cons hd tl =>
    if !p hd then
      (tl.waitUntil p).mapCheap fun ⟨l, e?⟩ => ⟨hd :: l, e?⟩
    else
      .pure ⟨[hd], none⟩
  | nil => .pure ⟨[], none⟩
  | delayed tl =>
    tl.bindCheap fun
      | .ok tl   => tl.waitUntil p
      | .error e => .pure ⟨[], some e⟩

/-- Spawns a `Task` waiting on all elements. -/
def waitAll : AsyncList ε α → ServerTask (List α × Option ε) :=
  waitUntil (fun _ => false)

/-- Spawns a `Task` acting like `List.find?` but which will wait for tail evaluation
when necessary to traverse the list. If the tail terminates before a matching element
is found, the task throws the terminating value. -/
partial def waitFind? (p : α → Bool) : AsyncList ε α → ServerTask (Except ε (Option α))
  | nil => .pure <| .ok none
  | cons hd tl =>
    if p hd then .pure <| Except.ok <| some hd
    else tl.waitFind? p
  | delayed tl =>
    tl.bindCheap fun
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
    if ← tl.hasFinished then
      match tl.get with
      | Except.ok tl => tl.getFinishedPrefix
      | Except.error e => pure ⟨[], some e, true⟩
    else pure ⟨[], none, false⟩

partial def getFinishedPrefixWithTimeout (xs : AsyncList ε α) (timeoutMs : UInt32)
    (cancelTk? : Option (ServerTask Unit) := none) : BaseIO (List α × Option ε × Bool) := do
  let timeoutTask : ServerTask (Unit ⊕ Except ε (AsyncList ε α)) ←
    if timeoutMs == 0 then
      pure <| ServerTask.pure (Sum.inl ())
    else
      ServerTask.BaseIO.asTask do
        IO.sleep timeoutMs
        return .inl ()
  go timeoutTask xs
where
  go (timeoutTask : ServerTask (Unit ⊕ Except ε (AsyncList ε α)))
      (xs : AsyncList ε α) : BaseIO (List α × Option ε × Bool) := do
    match xs with
    | cons hd tl =>
      let ⟨tl, e?, isComplete⟩ ← go timeoutTask tl
      return ⟨hd :: tl, e?, isComplete⟩
    | nil => return ⟨[], none, true⟩
    | delayed tl =>
      let tl : ServerTask (Except ε (AsyncList ε α)) := tl
      let tl := tl.mapCheap .inr
      let cancelTk? := do return (← cancelTk?).mapCheap .inl
      let tasks : { t : List _ // t.length > 0 } :=
        match cancelTk? with
        | none => ⟨[tl, timeoutTask], by exact Nat.zero_lt_succ _⟩
        | some cancelTk => ⟨[cancelTk, tl, timeoutTask], by exact Nat.zero_lt_succ _⟩
      let r ← ServerTask.waitAny tasks.val (h := tasks.property)
      match r with
      | .inl _ => return ⟨[], none, false⟩ -- Timeout or cancellation - stop waiting
      | .inr (.ok tl) => go timeoutTask tl
      | .inr (.error e) => return ⟨[], some e, true⟩

partial def getFinishedPrefixWithConsistentLatency (xs : AsyncList ε α) (latencyMs : UInt32)
    (cancelTk? : Option (ServerTask Unit) := none) : BaseIO (List α × Option ε × Bool) := do
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
    if ← cancelTk.hasFinished then
      return
    let sleepTask ← Lean.Server.ServerTask.BaseIO.asTask do
      IO.sleep sleepDurationMs
    ServerTask.waitAny [sleepTask, cancelTk]

end AsyncList

end IO
