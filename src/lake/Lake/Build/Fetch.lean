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

/-- The internal core monad of Lake builds. **Not intended for user use.** -/
@[deprecated "Deprecated without replacement." (since := "2025-02-22")]
abbrev CoreBuildM := BuildT LogIO

/--
A recursive build of a Lake build store that may encounter a cycle.

An internal monad. **Not intended for user use.**
-/
abbrev RecBuildT (m : Type → Type) :=
  CallStackT BuildKey <| StateRefT' IO.RealWorld BuildStore <| BuildT m

/-- Log build cycle and error. -/
@[specialize] def buildCycleError [MonadError m] (cycle : Cycle BuildKey) : m α :=
  error s!"build cycle detected:\n{"\n".intercalate <| cycle.map (s!"  {·}")}"

instance [Monad m] [MonadError m] : MonadCycleOf BuildKey (RecBuildT m) where
  throwCycle := buildCycleError

/--
A recursive build of a Lake build store that may encounter a cycle.

An internal monad. **Not intended for user use.**
-/
abbrev RecBuildM := RecBuildT LogIO

/-- Run a recursive build. -/
@[inline] def RecBuildT.run
  [Monad m] [MonadLiftT (ST IO.RealWorld) m]
  (stack : CallStack BuildKey) (store : BuildStore) (build : RecBuildT m α)
: BuildT m (α × BuildStore) :=
  build stack |>.run store

/-- Run a recursive build in a fresh build store. -/
@[inline] def RecBuildT.run'
  [Monad m] [MonadLiftT (ST IO.RealWorld) m] (build : RecBuildT m α)
: BuildT m α := do
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

/-- Fetch the result associated with the info using the Lake build index. -/
@[inline] def BuildInfo.fetch (self : BuildInfo) [FamilyOut BuildData self.key α] : FetchM (Job α) :=
  fun build => cast (by simp) <| build self

export BuildInfo (fetch)

/-- Fetch the result of this facet of a module. -/
protected def ModuleFacet.fetch (self : ModuleFacet α) (mod : Module) : FetchM (Job α) :=
  fetch <| mod.facetCore self.name
