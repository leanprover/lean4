/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Build.LeanLib

namespace Lake

-- # Build Package Executable

def LeanExe.target (self : LeanExe) : FileTarget :=
  BuildTarget.mk' self.file do
    let cTargetMap ← buildModuleFacetMap #[self.root] &`lean.c
    let pkgLinkTargets ← self.pkg.linkTargetsOf cTargetMap
    let linkTargets :=
      if self.pkg.isLocalModule self.root.name then
        pkgLinkTargets
      else
        let rootTarget := cTargetMap.find? self.root.name |>.get!
        let rootLinkTarget := self.root.mkOTarget <| Target.active rootTarget
        #[rootLinkTarget] ++ pkgLinkTargets
    let target := leanExeTarget self.file linkTargets self.linkArgs
    target.materializeAsync

protected def Package.exeTarget (self : Package) : FileTarget :=
  self.builtinExe.target
