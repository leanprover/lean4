/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Lean.Meta.Basic
import Lean.LibrarySuggestions.Basic
import Init.System.Platform

/-!
# Symbol frequency

Symbol frequencies for library suggestions are computed on first use and cached for the process.
The imported statements are traversed in parallel tasks. Index construction does not count against
the caller's heartbeat budget. Cancellation is checked during traversal and while waiting for
another caller's computation. Once their inputs are available, the frequency and trigger maps are
built without further cancellation checks, so later queries can reuse the cached results.
-/

namespace Lean.LibrarySuggestions

/--
A process-local cache for a value that is computed at most once at a time: `none` before first
use, then a task for the value, which is `none` if the computation failed.
-/
abbrev SharedCache (α : Type) := IO.Ref (Option (Task (Option α)))

/-- Process-local cache for the relevant constants of the imported theorems. -/
builtin_initialize importedRelevantConstantsRef : SharedCache (Array (Name × Array Name)) ←
  IO.mkRef none

/-- Process-local cache for the imported symbol frequencies. -/
builtin_initialize symbolFrequencyMapRef : SharedCache (NameMap Nat) ← IO.mkRef none

/-- Exclude index preparation from heartbeat accounting, while retaining cancellation. -/
def withUncountedHeartbeats (x : CoreM α) : CoreM α := do
  Core.checkSystem "library suggestion initialization"
  let heartbeats ← IO.getNumHeartbeats
  try
    withReader (fun ctx => { ctx with maxHeartbeats := 0 }) x
  finally
    IO.setNumHeartbeats heartbeats

/-- Wait for `t`, but throw an interrupt exception as soon as the caller is cancelled. -/
def waitInterruptibly (t : Task (Option α)) : CoreM (Option α) := do
  if ← IO.hasFinished t then
    return t.get
  let some tk := (← readThe Core.Context).cancelTk? | IO.wait t
  let result : IO.Promise (Option (Option α)) ← IO.Promise.new
  tk.onSet (result.resolve none)
  BaseIO.chainTask t (fun value => result.resolve (some value)) (sync := true)
  match ← IO.wait (result.resultD none) with
  | some result => return result
  | none => throwInterruptException

/--
The value in `cache`, computed with `x` on first use. Concurrent callers wait for the first
caller's computation instead of repeating it. A computation that fails or is interrupted is not
cached, and the callers that were waiting for it compute the value themselves.
-/
partial def SharedCache.getOrCompute (cache : SharedCache α) (x : CoreM α) : CoreM α := do
  let promise : IO.Promise (Option α) ← IO.Promise.new
  let running? ← cache.modifyGet fun
    | some t => (some t, some t)
    | none => (none, some (promise.resultD none))
  if let some t := running? then
    if let some value ← waitInterruptibly t then
      return value
    return ← cache.getOrCompute x
  try
    let value ← x
    cache.set (some (.pure (some value)))
    promise.resolve (some value)
    return value
  finally
    unless ← promise.isResolved do
      cache.set none
      promise.resolve none

/--
The relevant constants (see `Expr.relevantConstants`) of each imported theorem that library
suggestions consider, in the iteration order of `env.constants.map₁`. This is computed in parallel
tasks and cached on first use, assuming the imported environment remains fixed for the lifetime of
the process. Local declarations are not included. The array stays in memory for the rest of the
process.
-/
def importedRelevantConstants : CoreM (Array (Name × Array Name)) :=
  importedRelevantConstantsRef.getOrCompute <| withUncountedHeartbeats do
    let env ← getEnv
    let names := env.constants.map₁.keysArray.filter fun name =>
      !isDeniedPremise env name && wasOriginallyTheorem env name
    let cancelTk? := (← readThe Core.Context).cancelTk?
    let visitChunk (chunk : Array Name) : CoreM (Array (Name × Array Name)) :=
      Meta.MetaM.run' <| withoutExporting do
        let types ← chunk.mapM fun name => return (← getConstInfo name).type
        return chunk.zip (← Expr.relevantConstantsOfEach types cancelTk?)
    -- Chunks bound the size of each task's `MetaM` caches; more chunks repeat more work.
    let nTasks := max 1 (System.Platform.Internal.getHardwareConcurrency ()).toNat
    let chunkSize := max 1 ((names.size + nTasks - 1) / nTasks)
    let mut tasks := #[]
    for i in [0:nTasks] do
      let chunk := names.extract (i * chunkSize) ((i + 1) * chunkSize)
      if chunk.isEmpty then
        continue
      -- With a token, every `Core.checkSystem` in the task would read it, and concurrent reads
      -- of one `IO.Ref` spin. `relevantConstantsOfEach` checks `cancelTk?` every 64 statements.
      let act ← Core.wrapAsync visitChunk none
      tasks := tasks.push (← EIO.asTask (act chunk))
    let mut consts := Array.mkEmpty names.size
    for task in tasks do
      match ← IO.wait task with
      | .ok chunk => consts := consts ++ chunk
      | .error e => throw e
    return consts

/--
The symbol frequency map for imported constants. This is computed and cached on first use, assuming
the imported environment remains fixed for the lifetime of the process. Local declarations are not
included.
-/
public def symbolFrequencyMap : CoreM (NameMap Nat) :=
  symbolFrequencyMapRef.getOrCompute <| withUncountedHeartbeats do
    return (← importedRelevantConstants).foldl (init := ∅) fun acc (_, consts) =>
      consts.foldl (init := acc) fun acc n => acc.alter n fun count => some (count.getD 0 + 1)

/--
Return the number of times a `Name` appears
in the signatures of (non-internal) theorems in the imported environment,
skipping instance arguments and proofs.
-/
public def symbolFrequency (n : Name) : CoreM Nat :=
  return (← symbolFrequencyMap) |>.getD n 0
