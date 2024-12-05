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

/-! ## Helper Encoders -/

private local instance : BEq FilePath where
  beq a b := a.normalize == b.normalize

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

/-! ## Configuration Encoders -/

protected def WorkspaceConfig.toToml (cfg : WorkspaceConfig) (t : Table := {}) : Table :=
  t.insertD `packagesDir cfg.packagesDir defaultPackagesDir

instance : ToToml WorkspaceConfig := ⟨(toToml ·.toToml)⟩

def LeanConfig.toToml (cfg : LeanConfig) (t : Table := {}) : Table :=
  have : ToToml (Array LeanOption) := leanOptionsEncoder
  t.insertD `buildType cfg.buildType .release
  |>.smartInsert `backend cfg.backend
  |>.smartInsert `platformIndependent cfg.platformIndependent
  |>.smartInsert `leanOptions cfg.leanOptions
  |>.smartInsert `moreServerOptions cfg.moreServerOptions
  |>.smartInsert `moreLeanArgs cfg.moreLeanArgs
  |>.smartInsert `weakLeanArgs cfg.weakLeanArgs
  |>.smartInsert `moreLeancArgs cfg.moreLeancArgs
  |>.smartInsert `weakLeancArgs cfg.weakLeancArgs
  |>.smartInsert `moreLinkArgs cfg.moreLinkArgs
  |>.smartInsert `weakLinkArgs cfg.weakLinkArgs

instance : ToToml LeanConfig := ⟨(toToml ·.toToml)⟩
instance : ToToml LeanVer := ⟨(toToml <| toString ·)⟩

protected def PackageConfig.toToml (cfg : PackageConfig) (t : Table := {}) : Table :=
  t.insert `name cfg.name
  |>.insertD `precompileModules cfg.precompileModules false
  |>.smartInsert `moreGlobalServerArgs cfg.moreGlobalServerArgs
  |>.insertD `srcDir cfg.srcDir "."
  |>.insertD `buildDir cfg.buildDir defaultBuildDir
  |>.insertD `leanLibDir cfg.leanLibDir defaultLeanLibDir
  |>.insertD `nativeLibDir cfg.nativeLibDir defaultNativeLibDir
  |>.insertD `binDir cfg.binDir defaultBinDir
  |>.insertD `irDir cfg.irDir defaultIrDir
  |>.smartInsert `releaseRepo (cfg.releaseRepo <|> cfg.releaseRepo?)
  |>.insertD `buildArchive (cfg.buildArchive?.getD cfg.buildArchive) (defaultBuildArchive cfg.name)
  |>.insertD `preferReleaseBuild cfg.preferReleaseBuild false
  |>.insertD `version cfg.version {}
  |> smartInsertVerTags cfg.versionTags
  |>.smartInsert `keywords cfg.description
  |>.smartInsert `keywords cfg.keywords
  |>.smartInsert `homepage cfg.homepage
  |>.smartInsert `license cfg.license
  |>.insertD `licenseFiles cfg.licenseFiles #["LICENSE"]
  |>.insertD `readmeFile cfg.readmeFile "README.md"
  |>.insertD `reservoir cfg.reservoir true
  |> cfg.toWorkspaceConfig.toToml
  |> cfg.toLeanConfig.toToml
where
  smartInsertVerTags (pat : StrPat) (t : Table) : Table :=
    match pat with
    | .mem s => t.insert `versionTags (toToml s)
    | .startsWith p => t.insert `versionTags.startsWith (toToml p)
    | .satisfies _ n =>
      if n.isAnonymous || n == `default then t else
      t.insert `versionTags.preset (toToml n)

instance : ToToml PackageConfig := ⟨(toToml ·.toToml)⟩

instance : ToToml Glob := ⟨(toToml ·.toString)⟩

protected def LeanLibConfig.toToml (cfg : LeanLibConfig) (t : Table := {}) : Table :=
  t.insert `name cfg.name
  |>.insertD `srcDir cfg.srcDir "."
  |>.insertD `roots cfg.roots #[cfg.name]
  |>.insertD `globs cfg.globs (cfg.roots.map .one)
  |>.insertD `libName cfg.libName (cfg.name.toString (escape := false))
  |>.insertD `precompileModules cfg.precompileModules false
  |>.insertD `defaultFacets cfg.defaultFacets #[LeanLib.leanArtsFacet]
  |> cfg.toLeanConfig.toToml

instance : ToToml LeanLibConfig := ⟨(toToml ·.toToml)⟩

protected def LeanExeConfig.toToml (cfg : LeanExeConfig) (t : Table  := {}) : Table :=
  t.insert `name cfg.name
  |>.insertD `srcDir cfg.srcDir "."
  |>.insertD `root cfg.root cfg.name
  |>.insertD `exeName cfg.exeName (cfg.name.toStringWithSep "-" (escape := false))
  |>.insertD `supportInterpreter cfg.supportInterpreter false
  |> cfg.toLeanConfig.toToml

instance : ToToml LeanExeConfig := ⟨(toToml ·.toToml)⟩

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
  |>.smartInsert `lean_lib pkg.leanLibConfigs.toArray
  |>.smartInsert `lean_exe pkg.leanExeConfigs.toArray
