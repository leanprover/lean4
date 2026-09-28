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

Symbol frequencies for library suggestions are computed on first use, without storing any data in
olean files. The first query may be expensive for large imported libraries, so the imported
statements are traversed in parallel tasks. Index construction does not consume the caller's
heartbeat budget, but can be interrupted.
-/

namespace Lean.LibrarySuggestions

/-- Process-local cache for the relevant constants of the imported theorems. -/
builtin_initialize importedRelevantConstantsRef : IO.Ref (Option (Array (Name × Array Name))) ←
  IO.mkRef none

/-- Process-local cache for the imported symbol frequencies. -/
builtin_initialize symbolFrequencyMapRef : IO.Ref (Option (NameMap Nat)) ← IO.mkRef none

/-- Exclude index preparation from heartbeat accounting, while retaining cancellation. -/
def withUncountedHeartbeats (x : CoreM α) : CoreM α := do
  Core.checkSystem "library suggestion initialization"
  let heartbeats ← IO.getNumHeartbeats
  try
    withReader (fun ctx => { ctx with maxHeartbeats := 0 }) x
  finally
    IO.setNumHeartbeats heartbeats

/--
The relevant constants (see `Expr.relevantConstants`) of each imported theorem that library
suggestions consider, in the iteration order of `env.constants.map₁`. This is computed in parallel
tasks and cached on first use, assuming the imported environment remains fixed for the lifetime of
the process. Local declarations are not included.
-/
def importedRelevantConstants : CoreM (Array (Name × Array Name)) := do
  match ← importedRelevantConstantsRef.get with
  | some consts => return consts
  | none =>
    let consts ← withUncountedHeartbeats do
      let env ← getEnv
      let names := env.constants.map₁.keysArray.filter fun name =>
        !isDeniedPremise env name && wasOriginallyTheorem env name
      let cancelTk? := (← readThe Core.Context).cancelTk?
      let visitChunk (chunk : Array Name) : CoreM (Array (Name × Array Name)) :=
        Meta.MetaM.run' <| withoutExporting do
          let mut out := Array.mkEmpty chunk.size
          for start in [0:chunk.size:4096] do
            if let some tk := cancelTk? then
              if ← tk.isSet then
                throwInterruptException
            let names := chunk.extract start (start + 4096)
            let types ← names.mapM fun name => return (← getConstInfo name).type
            out := out ++ names.zip (← Expr.relevantConstantsOfEach types)
          return out
      -- One chunk per hardware thread: each task starts with empty `MetaM` caches, so more
      -- chunks repeat more work.
      let nTasks := max 1 (System.Platform.Internal.getHardwareConcurrency ()).toNat
      let chunkSize := max 1 ((names.size + nTasks - 1) / nTasks)
      let mut tasks := #[]
      for i in [0:nTasks] do
        let chunk := names.extract (i * chunkSize) ((i + 1) * chunkSize)
        if chunk.isEmpty then
          continue
        -- `visitChunk` checks `cancelTk?` once every 4096 theorems. Passing it to `wrapAsync` would
        -- have every `Core.checkSystem` in every task read the same `IO.Ref`, and concurrent reads
        -- of one `IO.Ref` spin.
        let act ← Core.wrapAsync visitChunk none
        tasks := tasks.push (← EIO.asTask (act chunk) (prio := .dedicated))
      let mut consts := Array.mkEmpty names.size
      for task in tasks do
        match ← IO.wait task with
        | .ok chunk => consts := consts ++ chunk
        | .error e => throw e
      return consts
    importedRelevantConstantsRef.set (some consts)
    return consts

/--
The symbol frequency map for imported constants. This is computed and cached on first use, assuming
the imported environment remains fixed for the lifetime of the process. Local declarations are not
included.
-/
public def symbolFrequencyMap : CoreM (NameMap Nat) := do
  match ← symbolFrequencyMapRef.get with
  | some map => return map
  | none =>
    let map ← withUncountedHeartbeats do
      return (← importedRelevantConstants).foldl (init := ∅) fun acc (_, consts) =>
        consts.foldl (init := acc) fun acc n => acc.alter n fun count => some (count.getD 0 + 1)
    symbolFrequencyMapRef.set (some map)
    return map

/--
Return the number of times a `Name` appears
in the signatures of (non-internal) theorems in the imported environment,
skipping instance arguments and proofs.
-/
public def symbolFrequency (n : Name) : CoreM Nat :=
  return (← symbolFrequencyMap) |>.getD n 0
