/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
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

/-- The top-level monad for Lake build functions. **Renamed `FetchM`.** -/
@[deprecated FetchM] abbrev IndexBuildM := FetchM

/-- The old build monad. **Uses should generally be replaced by `FetchM`.** -/
@[deprecated FetchM] abbrev BuildM := BuildT LogIO

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
    let (log, jobLog) := log.split iniPos
    let job := if jobLog.isEmpty then job else job.mapResult (sync := true)
      (·.modifyState (.modifyLog (jobLog ++  ·)))
    return (.ok job log, store)
  | (.error _ log, store) =>
    let (log, jobLog) := log.split iniPos
    return (.ok (.error jobLog) log, store)

/--
Registers the produced job for the top-level build monitor
(e.g., the Lake CLI progress UI), assigning it `caption`.

Stray I/O, logs, and errors produced by `x` will be wrapped into the job.
-/
@[inline] def withRegisterJob
  (caption : String) (x : FetchM (Job α))
: FetchM (Job α) := do
  let job ← ensureJob x
  let job := job.setCaption caption
  let regJob := job.mapResult (sync := true) discard
  (← readThe BuildContext).registeredJobs.modify (·.push regJob)
  return job.renew

/--
Registers the produced job for the top-level build monitor
if it is not already (i.e., it has an empty caption).
-/
@[inline] def maybeRegisterJob
  (fallbackCaption : String) (job : Job α)
: FetchM (Job α) := do
  if job.caption.isEmpty then
    let job := job.setCaption fallbackCaption
    let regJob := job.mapResult (sync := true) discard
    (← readThe BuildContext).registeredJobs.modify (·.push regJob)
    return job.renew
  else
    return job
