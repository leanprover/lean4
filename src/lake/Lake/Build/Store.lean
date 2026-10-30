/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lake.Util.Store
public import Lake.Build.Job.Basic

/-!
# The Lake Build Store

The Lake build store is the map of Lake build keys to build task and/or
build results that is slowly filled during a recursive build (e.g., via
topological-based build of an initial key's dependencies).
-/

namespace Lake
open Lean (Name NameMap)

/-- A monad equipped with a Lake build store. -/
public abbrev MonadBuildStore (m) := MonadDStore BuildKey (Job <| BuildData ·) m

/-- The type of the Lake build store. -/
public  abbrev BuildStore :=
  Std.DTreeMap BuildKey (Job <| BuildData ·) BuildKey.quickCmp

@[inline] public def BuildStore.empty : BuildStore := Std.DTreeMap.empty
