/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Util.Error
import Lake.Util.Cycle
import Lake.Util.EquipT
import Lake.Build.Info
import Lake.Build.Store

/-! # Recursive Building

This module defines Lake's top-level build monad, `FetchM`, used
for performing recursive builds. A recursive build is a build function
which can fetch the results of other (recursive) builds. This is done
using the `fetch` function defined in this module.
-/

namespace Lake

/-- A recursive build of a Lake build store that may encounter a cycle. -/
abbrev RecBuildM :=
  CallStackT BuildKey <| BuildT <| ELogT <| StateT BuildStore <| BaseIO

instance : MonadLift LogIO RecBuildM := ⟨ELogT.takeAndRun⟩

/--
Run a `JobM` action in `RecBuildM` (and thus `FetchM`).

Generally, this should not be done, and instead a job action
should be run asynchronously in a Job (e.g., via `Job.async`).
-/
@[inline] def RecBuildM.runJobM (x : JobM α) : RecBuildM α := fun _ ctx log store => do
  match (← x ctx {log}) with
  | .ok a s => return (.ok a s.log, store)
  | .error e s => return (.error e s.log, store)

instance : MonadLift JobM RecBuildM := ⟨RecBuildM.runJobM⟩

/-- Run a recursive build. -/
@[inline] def RecBuildM.run
  (stack : CallStack BuildKey) (store : BuildStore) (build : RecBuildM α)
: CoreBuildM (α × BuildStore) := fun ctx log => do
  match (← build stack ctx log store) with
  | (.ok a log, store) => return .ok (a, store) log
  | (.error e log, _) => return .error e log

/-- Run a recursive build in a fresh build store. -/
@[inline] def RecBuildM.run' (build : RecBuildM α) : CoreBuildM α := do
  (·.1) <$> build.run {} {}

/-- Log build cycle and error. -/
@[specialize] def buildCycleError [MonadError m] (cycle : Cycle BuildKey) : m α :=
  error s!"build cycle detected:\n{"\n".intercalate <| cycle.map (s!"  {·}")}"

instance : MonadCycleOf BuildKey RecBuildM where
  throwCycle := buildCycleError

/-- A build function for any element of the Lake build index. -/
abbrev IndexBuildFn (m : Type → Type v) :=
  -- `DFetchFn BuildInfo (BuildData ·.key) m` with less imports
  (info : BuildInfo) → m (BuildData info.key)

/-- A transformer to equip a monad with a build function for the Lake index. -/
abbrev IndexT (m : Type → Type v) := EquipT (IndexBuildFn m) m

/-- The top-level monad for Lake build functions. -/
abbrev FetchM := IndexT RecBuildM

/-- Ensures that `JobM` lifts into `FetchM`. -/
example : MonadLiftT JobM FetchM := inferInstance

/-- Ensures that `SpawnM` lifts into `FetchM`. -/
example : MonadLiftT SpawnM FetchM := inferInstance

/-- The top-level monad for Lake build functions. **Renamed `FetchM`.** -/
@[deprecated FetchM (since := "2024-04-30")] abbrev IndexBuildM := FetchM

/-- The old build monad. **Uses should generally be replaced by `FetchM`.** -/
@[deprecated FetchM (since := "2024-04-30")] abbrev BuildM := BuildT LogIO

/-- Fetch the result associated with the info using the Lake build index. -/
@[inline] def BuildInfo.fetch (self : BuildInfo) [FamilyOut BuildData self.key α] : FetchM α :=
  fun build => cast (by simp) <| build self

export BuildInfo (fetch)

/-- Wraps stray I/O, logs, and errors in `x` into the produced job.  -/
def ensureJob (x : FetchM (Job α))
: FetchM (Job α) := fun fetch stack ctx log store => do
  let iniPos := log.endPos
  match (← (withLoggedIO x) fetch stack ctx log store) with
  | (.ok job log, store) =>
    if iniPos < log.endPos then
      let (log, jobLog) := log.split iniPos
      let job := job.mapResult (sync := true) (·.prependLog jobLog)
      return (.ok job log, store)
    else
      return (.ok job log, store)
  | (.error _ log, store) =>
    let (log, jobLog) := log.split iniPos
    return (.ok (.error jobLog) log, store)

/--
Registers the job for the top-level build monitor,
(e.g., the Lake CLI progress UI), assigning it `caption`.
-/
def registerJob (caption : String) (job : Job α) (optional := false) : FetchM (Job α) := do
  let job : Job α := {job with caption, optional}
  (← getBuildContext).registeredJobs.modify (·.push job)
  return job.renew

/--
Registers the produced job for the top-level build monitor
(e.g., the Lake CLI progress UI), assigning it `caption`.

Stray I/O, logs, and errors produced by `x` will be wrapped into the job.
-/
def withRegisterJob
  (caption : String) (x : FetchM (Job α)) (optional := false)
: FetchM (Job α) := do
  let job ← ensureJob x
  registerJob caption job optional

/--
Registers the produced job for the top-level build monitor
if it is not already (i.e., it has an empty caption).
-/
@[inline] def maybeRegisterJob
  (caption : String) (job : Job α)
: FetchM (Job α) := do
  if job.caption.isEmpty then
    registerJob caption job
  else
    return job
