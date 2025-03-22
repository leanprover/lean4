/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Toml.Encode
import Lake.Config.Package

/-! # TOML Translation

Converts a declarative Lake configuration into a TOML table.
-/

namespace Lake
open Lean System Toml

/-! ## General Helpers -/

private local instance : BEq FilePath where
  beq a b := a.normalize == b.normalize

class InsertField (σ : Type u) (name : Name) where
  insertField : σ → Table → Table

abbrev Toml.Table.insertField
  (cfg : σ) (name : Name) [field : InsertField σ name] (t : Table)
: Table := InsertField.insertField name cfg t

instance [SmartInsert α] [field : ConfigField σ name α] : InsertField σ name where
  insertField cfg t := t.smartInsert name (field.get cfg)

instance [ToToml α] [BEq α] [field : ConfigField σ name α] : InsertField σ name where
  insertField cfg t := t.insertD name (field.get cfg) (field.mkDefault cfg)

/-! ## Value Encoders -/

instance : ToToml Backend := ⟨(toToml ·.toString)⟩

instance : SmartInsert Backend where
  smartInsert k v t := match v with | .default => t | v => t.insert k (toToml v)

instance : ToToml BuildType := ⟨(toToml ·.toString)⟩

def Toml.encodeLeanOptionValue (v : LeanOptionValue) : Value :=
  match v with
  | .ofString s => toToml s
  | .ofBool b => toToml b
  | .ofNat n => toToml n

instance : ToToml LeanOptionValue := ⟨encodeLeanOptionValue⟩

def Toml.encodeLeanOptions (opts : Array LeanOption) : Table :=
  opts.foldl (init := {}) fun vs ⟨k,v⟩ => vs.insert k (toToml v)

def Toml.leanOptionsEncoder : ToToml (Array LeanOption) where
  toToml opts := .table .missing <| encodeLeanOptions opts

def smartInsertVerTags (pat : StrPat) (t : Table) : Table :=
  match pat with
  | .mem s => t.insert `versionTags (toToml s)
  | .startsWith p => t.insert `versionTags.startsWith (toToml p)
  | .satisfies _ n =>
    if n.isAnonymous || n == `default then t else
    t.insert `versionTags.preset (toToml n)

instance : InsertField (PackageConfig n) `versionTags where
  insertField cfg := smartInsertVerTags cfg.versionTags

/-! ## Package & Target Configuration Encoders -/

protected def WorkspaceConfig.toToml (cfg : WorkspaceConfig) (t : Table := {}) : Table :=
  t.insertField cfg `packagesDir

instance : ToToml WorkspaceConfig := ⟨(toToml ·.toToml)⟩

def LeanConfig.toToml (cfg : LeanConfig) (t : Table := {}) : Table :=
  have : ToToml (Array LeanOption) := leanOptionsEncoder
  t.insertField cfg `buildType
  |>.insertField cfg `backend
  |>.insertField cfg `platformIndependent
  |>.insertField cfg `leanOptions
  |>.insertField cfg `moreServerOptions
  |>.insertField cfg `moreLeanArgs
  |>.insertField cfg `weakLeanArgs
  |>.insertField cfg `moreLeancArgs
  |>.insertField cfg `weakLeancArgs
  |>.insertField cfg `moreLinkArgs
  |>.insertField cfg `weakLinkArgs

instance : ToToml LeanConfig := ⟨(toToml ·.toToml)⟩
instance : ToToml LeanVer := ⟨(toToml <| toString ·)⟩

protected def PackageConfig.toToml (cfg : PackageConfig n) (t : Table := {}) : Table :=
  t.insert `name n
  |>.insertField cfg `precompileModules
  |>.insertField cfg `moreGlobalServerArgs
  |>.insertField cfg `srcDir
  |>.insertField cfg `buildDir
  |>.insertField cfg `leanLibDir
  |>.insertField cfg `nativeLibDir
  |>.insertField cfg `binDir
  |>.insertField cfg `irDir
  |>.insertField cfg `releaseRepo
  |>.insertField cfg `buildArchive
  |>.insertField cfg `preferReleaseBuild
  |>.insertField cfg `version
  |>.insertField cfg `versionTags
  |>.insertField cfg `description
  |>.insertField cfg `keywords
  |>.insertField cfg `homepage
  |>.insertField cfg `license
  |>.insertField cfg `licenseFiles
  |>.insertField cfg `readmeFile
  |>.insertField cfg `reservoir
  |> cfg.toWorkspaceConfig.toToml
  |> cfg.toLeanConfig.toToml

instance : ToToml (PackageConfig n) := ⟨(toToml ·.toToml)⟩

instance : ToToml Glob := ⟨(toToml ·.toString)⟩

protected def LeanLibConfig.toToml (cfg : LeanLibConfig n) (t : Table := {}) : Table :=
  t.insert `name n
  |>.insertField cfg `srcDir
  |>.insertField cfg `roots
  |>.insertField cfg `globs
  |>.insertField cfg `libName
  |>.insertField cfg `precompileModules
  |>.insertField cfg `defaultFacets
  |> cfg.toLeanConfig.toToml

instance : ToToml (LeanLibConfig n) := ⟨(toToml ·.toToml)⟩

protected def LeanExeConfig.toToml (cfg : LeanExeConfig n) (t : Table  := {}) : Table :=
  t.insert `name n
  |>.insertField cfg `srcDir
  |>.insertField cfg `root
  |>.insertField cfg `exeName
  |>.insertField cfg `supportInterpreter
  |> cfg.toLeanConfig.toToml

instance : ToToml (LeanExeConfig n) := ⟨(toToml ·.toToml)⟩

/-! ## Dependency Configuration Encoders -/

protected def Dependency.toToml (dep : Dependency) (t : Table  := {}) : Table :=
  let t := t
    |>.insert `name dep.name
    |>.insertD `scope dep.scope ""
    |>.smartInsert `version dep.version?
  let t :=
    if let some src := dep.src? then
      match src with
      | .path dir => t.insert `path (toToml dir)
      | .git url rev subDir? =>
        t.insert `git url
        |>.smartInsert `rev rev
        |>.smartInsert `subDir subDir?
    else
      t
  t.smartInsert `options <| dep.opts.fold (·.insert · ·) Table.empty

instance : ToToml Dependency := ⟨(toToml ·.toToml)⟩

/-! ## Root Encoder -/

/-- Create a TOML table that encodes the declarative configuration of the package. -/
def Package.mkTomlConfig (pkg : Package) (t : Table := {}) : Table :=
  pkg.config.toToml t
  |>.smartInsert `testDriver pkg.testDriver
  |>.smartInsert `testDriverArgs pkg.testDriverArgs
  |>.smartInsert `lintDriver pkg.lintDriver
  |>.smartInsert `lintDriverArgs pkg.lintDriverArgs
  |>.smartInsert `defaultTargets pkg.defaultTargets
  |>.smartInsert `require pkg.depConfigs
  |>.smartInsert `lean_lib (pkg.targetDecls.filterMap (·.leanLibConfig?.map toToml))
  |>.smartInsert `lean_exe (pkg.targetDecls.filterMap (·.leanExeConfig?.map toToml))
