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

/-! # Recursive Building  -/

namespace Lake

/-- A recursive build of a Lake build store that may encounter a cycle. -/
abbrev RecBuildM := CallStackT BuildKey <| StateT BuildStore <| CoreBuildM

/-- Log build cycle and error. -/
@[specialize] def buildCycleError [MonadError m] (cycle : Cycle BuildKey) : m α :=
  error s!"build cycle detected:\n{"\n".intercalate <| cycle.map (s!"  {·}")}"

instance : MonadCycleOf BuildKey RecBuildM where
  getCallStack := read
  withCallStack s x := x s
  throwCycle := buildCycleError

/-- A build function for any element of the Lake build index. -/
abbrev IndexBuildFn (m : Type → Type v) :=
  -- `DFetchFn BuildInfo (BuildData ·.key) m` with less imports
  (info : BuildInfo) → m (BuildData info.key)

/-- A transformer to equip a monad with a build function for the Lake index. -/
abbrev IndexT (m : Type → Type v) := EquipT (IndexBuildFn m) m

/-- The top-level monad for Lake build functions. -/
abbrev FetchM := IndexT RecBuildM

/-- Fetch the result associated with the info using the Lake build index. -/
@[inline] def BuildInfo.fetch (self : BuildInfo) [FamilyOut BuildData self.key α] : FetchM α :=
  fun build => cast (by simp) <| build self

export BuildInfo (fetch)
