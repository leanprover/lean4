/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Build.Module
import Lake.Build.Package
import Lake.Build.Library
import Lake.Build.Executable
import Lake.Build.ExternLib

/-! # Initial Facets -/

namespace Lake

/-- The initial set of Lake facets. -/
def initFacetConfigs : DNameMap FacetConfig :=
  DNameMap.empty
  |> insert Module.initFacetConfigs
  |> insert Package.initFacetConfigs
  |> insert LeanLib.initFacetConfigs
  |> insert LeanExe.initFacetConfigs
  |> insert ExternLib.initFacetConfigs
where
  insert {k} (group : DNameMap (KFacetConfig k)) map :=
    group.fold (init := map) fun m k v => m.insert k v.toFacetConfig
