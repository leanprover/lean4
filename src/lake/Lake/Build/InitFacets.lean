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
def initFacetConfigs : FacetMap :=
  FacetMap.empty
  |>.insert `module Module.initFacetConfigs
  |>.insert `package Package.initFacetConfigs
  |>.insert `leanLib LeanLib.initFacetConfigs
  |>.insert `leanExe LeanExe.initFacetConfigs
  |>.insert `externLib ExternLib.initFacetConfigs
