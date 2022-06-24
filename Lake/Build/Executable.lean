/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Build.Library

open Std System
open Lean (Name NameMap)

namespace Lake

-- # Build Package Executable

def Package.mkExeTarget (self : Package) (exe : LeanExeConfig) : FileTarget :=
  let exeFile := self.binDir / exe.fileName
  BuildTarget.mk' exeFile do
    let root : Module := ⟨self, WfName.ofName exe.root⟩
    let cTargetMap ← buildModuleFacetMap #[root] &`lean.c
    let pkgLinkTargets ← self.linkTargetsOf cTargetMap
    let linkTargets :=
      if self.isLocalModule exe.root then
        pkgLinkTargets
      else
        let rootTarget := cTargetMap.find? root.name |>.get!
        let rootLinkTarget := root.mkOTarget <| Target.active rootTarget
        #[rootLinkTarget] ++ pkgLinkTargets
    let target := leanExeTarget exeFile linkTargets exe.linkArgs
    target.materializeAsync

protected def Package.exeTarget (self : Package) : FileTarget :=
  self.mkExeTarget self.builtinExeConfig
