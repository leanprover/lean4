/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Util.Paths
import Lake.Config.Opaque
import Lake.Config.WorkspaceConfig
import Lake.Config.Package
import Lake.Config.Module

open System
open Lean (Name NameMap LeanPaths)

namespace Lake

/-- The file name of a workspace's package manifest (i.e., `manifest.json`). -/
def manifestFileName := "manifest.json"

/-- A Lake workspace -- the top-level package directory. -/
structure Workspace where
  /-- The root package of the workspace. -/
  root : Package
  /-- Name-package map of packages within the workspace. -/
  packageMap : NameMap Package := {}
  deriving Inhabited

namespace OpaqueWorkspace

unsafe def unsafeMk (ws : Workspace) : OpaqueWorkspace :=
  unsafeCast ws

@[implementedBy unsafeMk] constant mk (ws : Workspace) : OpaqueWorkspace

instance : Coe Workspace OpaqueWorkspace := ⟨mk⟩
instance : Inhabited OpaqueWorkspace := ⟨mk Inhabited.default⟩

unsafe def unsafeGet (self : OpaqueWorkspace) : Workspace :=
  unsafeCast self

@[implementedBy unsafeGet] constant get (self : OpaqueWorkspace) : Workspace

instance : Coe OpaqueWorkspace Workspace := ⟨get⟩

@[simp] axiom get_mk {ws : Workspace} : get (mk ws) = ws

end OpaqueWorkspace

namespace Workspace

/-- Create a `Workspace` from a package using its directory and `WorkspaceConfig`. -/
def ofPackage (pkg : Package) : Workspace :=
  {root := pkg}

/-- The path to the workspace's directory (i.e., the directory of the root package). -/
def dir (self : Workspace) : FilePath :=
  self.root.dir

/-- The workspace's configuration. -/
def config (self : Workspace) : WorkspaceConfig :=
  self.root.config.toWorkspaceConfig

/-- The workspace's `dir` joined with its `packagesDir` configuration. -/
def packagesDir (self : Workspace) : FilePath :=
  self.dir / self.config.packagesDir

/-- The workspace's JSON manifest of packages. -/
def manifestFile (self : Workspace) : FilePath :=
  self.packagesDir / manifestFileName

/-- The `List` of packages to the workspace. -/
def packageList (self : Workspace) : List Package :=
  self.packageMap.revFold (fun pkgs _ pkg => pkg :: pkgs) []

/-- The `Array` of packages to the workspace. -/
def packageArray (self : Workspace) : Array Package :=
  self.packageMap.fold (fun pkgs _ pkg => pkgs.push pkg) #[]

/-- Add a package to the workspace. -/
def addPackage (pkg : Package) (self : Workspace) : Workspace :=
  {self with packageMap := self.packageMap.insert pkg.name pkg}

/-- Get a package within the workspace by name. -/
def findPackage? (pkg : Name) (self : Workspace) : Option Package :=
  self.packageMap.find? pkg

/-- Check if the module is local to any package in the workspace. -/
def isLocalModule (mod : Name) (self : Workspace) : Bool :=
  self.packageMap.any fun _ pkg => pkg.isLocalModule mod

/-- Locate the named module in the workspace (if it is local to it). -/
def findModule? (mod : Name) (self : Workspace) : Option Module :=
  self.packageArray.findSome? (·.findModule? mod)

/-- Get the workspace's library configuration with the given name. -/
def findLeanLib? (name : Name) (self : Workspace) : Option (Package × LeanLibConfig) :=
  self.packageArray.findSome? fun pkg => pkg.findLeanLib? name <&> (pkg, ·)

/-- Get the workspace's executable configuration with the given name. -/
def findLeanExe? (name : Name) (self : Workspace) : Option (Package × LeanExeConfig) :=
  self.packageArray.findSome? fun pkg => pkg.findLeanExe? name <&> (pkg, ·)

/-- Get the workspace's external library with the given name. -/
def findExternLib? (name : Name) (self : Workspace) : Option (Package × ExternLibConfig) :=
  self.packageArray.findSome? fun pkg => pkg.findExternLib? name <&> (pkg, ·)

/-- The `LEAN_PATH` of the workspace. -/
def oleanPath (self : Workspace) : SearchPath :=
  self.packageList.map (·.oleanDir)

/-- The `LEAN_SRC_PATH` of the workspace. -/
def leanSrcPath (self : Workspace) : SearchPath :=
  self.packageList.map (·.srcDir)

/-- The `LeanPaths` of the workspace. -/
def leanPaths (self : Workspace) : LeanPaths :=
  let pkgs := self.packageList
  { oleanPath := pkgs.map (·.oleanDir), srcPath := pkgs.map (·.srcDir) }
