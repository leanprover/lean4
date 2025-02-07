/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Util.Lift
import Lake.Util.Error
import Lake.Util.Cycle
import Lake.Util.EquipT
import Lake.Build.Info
import Lake.Build.Store
import Lake.Build.Context

/-! # Recursive Building

This module defines Lake's top-level build monad, `FetchM`, used
for performing recursive builds. A recursive build is a build function
which can fetch the results of other (recursive) builds. This is done
using the `fetch` function defined in this module.
-/

namespace Lake

/-- The internal core monad of Lake builds. Not intended for user use. -/
abbrev CoreBuildM := BuildT LogIO

/--
A recursive build of a Lake build store that may encounter a cycle.

An internal monad. Not intended for user use.
-/
abbrev RecBuildT (m : Type → Type) :=
  CallStackT BuildKey <| StateRefT' IO.RealWorld BuildStore <| BuildT m

@[specialize] def formatCycle [ToString κ] (cycle : Cycle κ) : String :=
  "\n".intercalate <| cycle.map (s!"  {·}")

/-- Log build cycle and error. -/
@[inline] def buildCycleError [MonadError m] (cycle : Cycle BuildKey) : m α :=
  error s!"build cycle detected:\n{formatCycle cycle}"

instance [Monad m] [MonadError m] : MonadCycleOf BuildKey (RecBuildT m) where
  throwCycle := buildCycleError

/--
A recursive build of a Lake build store that may encounter a cycle.

An internal monad. Not intended for user use.
-/
abbrev RecBuildM := RecBuildT LogIO

/-- Run a recursive build. -/
@[inline] def RecBuildM.run
  (stack : CallStack BuildKey) (store : BuildStore) (build : RecBuildM α)
: CoreBuildM (α × BuildStore) :=
  build stack |>.run store

/-- Run a recursive build in a fresh build store. -/
@[inline] def RecBuildM.run' (build : RecBuildM α) : CoreBuildM α := do
  (·.1) <$> build.run {} {}

/-- A build function for any element of the Lake build index. -/
abbrev IndexBuildFn (m : Type → Type v) :=
  -- `DFetchFn BuildInfo (Job <| BuildData ·.key) m` with less imports
  (info : BuildInfo) → m (Job (BuildData info.key))

/-- A transformer to equip a monad with a build function for the Lake index. -/
abbrev IndexT (m : Type → Type v) := EquipT (IndexBuildFn RecBuildM) m

/-- The top-level monad transformer for Lake build functions. -/
abbrev FetchT (m : Type → Type) := IndexT <| RecBuildT m

/-- The top-level monad for Lake build functions. -/
abbrev FetchM := FetchT LogIO

/-- The top-level monad for Lake build functions. **Renamed `FetchM`.** -/
@[deprecated FetchM (since := "2024-04-30")] abbrev IndexBuildM := FetchM

/-- The old build monad. **Uses should generally be replaced by `FetchM`.** -/
@[deprecated FetchM (since := "2024-04-30")] abbrev BuildM := BuildT LogIO

/-- Fetch the result associated with the info using the Lake build index. -/
@[inline] def BuildInfo.fetch (self : BuildInfo) [FamilyOut BuildData self.key α] : FetchM (Job α) :=
  fun build => cast (by simp) <| build self

export BuildInfo (fetch)
