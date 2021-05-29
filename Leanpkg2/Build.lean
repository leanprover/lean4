/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Leanpkg2.Resolve
import Leanpkg2.BuildCore
import Leanpkg2.Configure
import Leanpkg2.Make

open System

namespace Leanpkg2

def buildImports (manifest : Manifest) (imports : List String) (leanArgs : List String) : IO Unit := do
  let cfg ← configure manifest
  let imports := imports.map (·.toName)
  let root ← getRootPart <| manifest.effectivePath
  let localImports := imports.filter (·.getRoot == root)
  if localImports != [] then
    let buildCfg : Build.Config := { pkg := root, leanArgs, leanPath := cfg.leanPath, moreDeps := cfg.moreDeps }
    if ← FilePath.pathExists "Makefile" then
      let oleans := localImports.map fun i => Lean.modToFilePath "build" i "olean" |>.toString
      execMake manifest oleans buildCfg
    else
      Build.buildModules buildCfg localImports
  IO.println cfg.leanPath
  IO.println cfg.leanSrcPath

def build (manifest : Manifest) (makeArgs leanArgs : List String := []) : IO Unit := do
  let cfg ← configure manifest
  let root ← getRootPart <| manifest.effectivePath
  let buildCfg : Build.Config := { pkg := root, leanArgs, leanPath := cfg.leanPath, moreDeps := cfg.moreDeps }
  --if makeArgs != [] || (← FilePath.pathExists "Makefile") then
  execMake manifest makeArgs buildCfg
  --else
  -- Build.buildModules buildCfg [root]
