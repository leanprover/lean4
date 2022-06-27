/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Build.Info
import Lake.Build.Store
import Lake.Build.Targets

namespace Lake

variable [Monad m] [MonadLiftT BuildM m] [MonadBuildStore m]

-- # Build Static Lib

/-- Build a library and its imports and collect its local modules' o files. -/
@[specialize] def LeanLib.recBuildOFiles
(self : LeanLib) (mods : Array Module) : IndexT m (Array ActiveFileTarget) := do
  have : MonadLift BuildM m := ⟨liftM⟩
  let mut targets := #[]
  let mut modSet := ModuleSet.empty
  for mod in mods do
    let (_, mods) ← mod.recBuildFacet &`lean.imports
    let mods := mods.push mod
    for mod in mods do
      unless modSet.contains mod do
        if self.isLocalModule mod.name then
          targets := targets.push <| ← mod.recBuildFacet &`lean.o
        modSet := modSet.insert mod
  return targets

protected def LeanLib.recBuildStatic (self : LeanLib) : IndexT m ActiveFileTarget := do
  have : MonadLift BuildM m := ⟨liftM⟩
  let oTargets := (← self.recBuildOFiles (← self.getModuleArray)).map Target.active
  staticLibTarget self.staticLibFile oTargets |>.activate

-- # Build Shared Lib

/-- Build and collect the o files and external libraries of a library and its imports. -/
@[specialize] def LeanLib.recBuildLinks
(self : LeanLib) (mods : Array Module) : IndexT m (Array ActiveFileTarget) := do
  have : MonadLift BuildM m := ⟨liftM⟩
  -- Build and collect modules
  let mut pkgs := #[]
  let mut pkgSet := PackageSet.empty
  let mut modSet := ModuleSet.empty
  let mut targets := #[]
  for mod in mods do
    let (_, mods) ← mod.recBuildFacet &`lean.imports
    let mods := mods.push mod
    for mod in mods do
      unless modSet.contains mod do
        unless pkgSet.contains mod.pkg do
            pkgSet := pkgSet.insert mod.pkg
            pkgs := pkgs.push mod.pkg
        if self.isLocalModule mod.name then
          targets := targets.push <| ← mod.recBuildFacet &`lean.o
        modSet := modSet.insert mod
  -- Build and collect external library targets
  for pkg in pkgs do
    let externLibTargets ← pkg.externLibs.mapM (·.recBuildShared)
    for target in externLibTargets do
      targets := targets.push target
  return targets

protected def LeanLib.recBuildShared (self : LeanLib) : IndexT m ActiveFileTarget := do
  have : MonadLift BuildM m := ⟨liftM⟩
  let linkTargets := (← self.recBuildLinks (← self.getModuleArray)).map Target.active
  leanSharedLibTarget self.sharedLibFile linkTargets self.linkArgs |>.activate

-- # Build Executable

def LeanExe.recBuild (self : LeanExe) : IndexT m ActiveFileTarget := do
  have : MonadLift BuildM m := ⟨liftM⟩
  let linkTargets := #[Target.active <| ← self.root.recBuildFacet &`lean.o]
  let (_, imports) ← self.root.recBuildFacet &`lean.imports
  let mut linkTargets ← imports.foldlM (init := linkTargets) fun a m => do
    return a.push <| Target.active <| ← m.recBuildFacet &`lean.o
  let deps := (← self.pkg.recBuildFacet &`deps).push self.pkg
  for dep in deps do for lib in dep.externLibs do
    linkTargets := linkTargets.push <| Target.active <| ← lib.recBuildStatic
  leanExeTarget self.file linkTargets self.linkArgs |>.activate
