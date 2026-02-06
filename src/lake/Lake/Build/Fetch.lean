/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lake.Build.Info
public import Lake.Build.Store
public import Lake.Build.Context
public import Lake.Config.Module
public import Lake.Util.EquipT
public import Lake.Util.Cycle
import Lake.Build.Infos

/-! # Recursive Building

This module defines Lake's top-level build monad, `FetchM`, used
for performing recursive builds. A recursive build is a build function
which can fetch the results of other (recursive) builds. This is done
using the `fetch` function defined in this module.
-/

namespace Lake

/-- A type alias for `Option Package` that assists monad type class synthesis. -/
@[expose] public def CurrPackage := Option Package

/-- Run the action `x` with `pkg?` as the current package or no package if `none`. -/
@[inline] public def withCurrPackage? [MonadWithReader CurrPackage m] (pkg? : Option Package) (x : m α): m α :=
  withReader (fun _ => pkg?) x

/-- Run the action `x` with `pkg` as the current package. -/
@[inline] public def withCurrPackage [MonadWithReader CurrPackage m] (pkg : Package) (x : m α): m α :=
  withCurrPackage? pkg x

/-- Get the package of the context (if any). -/
@[inline] public def getCurrPackage? [MonadReaderOf CurrPackage m] : m (Option Package) := read

/--
A recursive build of a Lake build store that may encounter a cycle.

An internal monad. **Not intended for user use.**
-/
public abbrev RecBuildT (m : Type → Type) :=
  ReaderT CurrPackage <| CallStackT BuildKey <| StateRefT' IO.RealWorld BuildStore <| BuildT m

/-- Build cycle error message. -/
public def buildCycleError (cycle : Cycle BuildKey) : String :=
  s!"build cycle detected:\n{formatCycle cycle}"

public instance [Monad m] [MonadError m] : MonadCycleOf BuildKey (RecBuildT m) where
  throwCycle cycle := error (buildCycleError cycle)

/--
A recursive build of a Lake build store that may encounter a cycle.

An internal monad. **Not intended for user use.**
-/
public abbrev RecBuildM := RecBuildT LogIO

/-- Run a recursive build. -/
@[inline] public def RecBuildT.run
  [Monad m] [MonadLiftT (ST IO.RealWorld) m]
  (stack : CallStack BuildKey) (store : BuildStore) (build : RecBuildT m α)
: BuildT m (α × BuildStore) := build none stack |>.run store

/-- Run a recursive build in a fresh build store. -/
@[inline] public def RecBuildT.run'
  [Monad m] [MonadLiftT (ST IO.RealWorld) m] (build : RecBuildT m α)
: BuildT m α := (·.1) <$> build.run {} {}

/-- A build function for any element of the Lake build index. -/
public abbrev IndexBuildFn (m : Type → Type v) :=
  -- `DFetchFn BuildInfo (Job <| BuildData ·.key) m` with less imports
  (info : BuildInfo) → m (Job (BuildData info.key))

/-- A transformer to equip a monad with a build function for the Lake index. -/
public abbrev IndexT (m : Type → Type v) := EquipT (IndexBuildFn RecBuildM) m

/-- The top-level monad transformer for Lake build functions. -/
public abbrev FetchT (m : Type → Type) := IndexT <| RecBuildT m

/-- The top-level monad for Lake build functions. -/
public abbrev FetchM := FetchT LogIO

/-- Construct a `FetchM` monad from its full functional representation. -/
@[inline] public def FetchM.ofFn
  (f : IndexBuildFn RecBuildM → Option Package → CallStack BuildKey →
    IO.Ref BuildStore → BuildContext → Log → BaseIO (EResult Log.Pos Log α))
: FetchM α := .mk fun fetch => fun pkg? stack store ctx => .mk fun log =>
  f fetch pkg? stack store ctx log

/-- Convert a `FetchM` monad to its full functional representation. -/
@[inline] public def FetchM.toFn (self : FetchM α) :
  IndexBuildFn RecBuildM → Option Package → CallStack BuildKey →
    IO.Ref BuildStore → BuildContext → Log → BaseIO (EResult Log.Pos Log α)
:= fun fetch pkg? stack store ctx log => self.run fetch pkg? stack store ctx |>.run log

/-- Fetch the result associated with the info using the Lake build index. -/
@[inline] public def BuildInfo.fetch (self : BuildInfo) [FamilyOut BuildData self.key α] : FetchM (Job α) :=
  .mk fun build => cast (by simp) <| build self

export BuildInfo (fetch)

/-- Fetch the result of this facet of a module. -/
public protected def ModuleFacet.fetch (self : ModuleFacet α) (mod : Module) : FetchM (Job α) :=
  fetch <| mod.facetCore self.name
