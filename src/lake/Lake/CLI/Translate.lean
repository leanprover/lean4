/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Load
import Lake.Config.Lang

namespace Lake
open Lean System Toml

class ToToml (α : Type u) where
  toToml : α → Value

export ToToml (toToml)

instance : ToToml String := ⟨.string .missing⟩
instance : ToToml FilePath := ⟨(·.toString)⟩
instance : ToToml Name := ⟨(·.toString)⟩
instance : ToToml Int := ⟨.integer .missing⟩
instance : ToToml Nat := ⟨fun n => .integer .missing (.ofNat n)⟩
instance : ToToml Float := ⟨.float .missing⟩
instance : ToToml Bool := ⟨.boolean .missing⟩
instance [ToToml α] : ToToml (Array α) := ⟨(·.map toToml)⟩
instance : ToToml Table := ⟨.table .missing⟩
instance : ToToml Value := ⟨id⟩

@[inline] def insertSome [ToToml α] (k : Name) (v? : Option α) (t : Table) : Table :=
  t.insertSome k (v?.map toToml)

/-- Inserts the value into the table if its is not equal to `default`. -/
@[inline] def insertD [ToToml α] [BEq α] (k : Name) (v : α) (default : α) (t : Table) : Table :=
  t.insertUnless (v == default) k (toToml v)

@[inline] def insertNotEmpty [ToToml α] (k : Name) (v : Array α) (t : Table) : Table :=
  t.insertUnless v.isEmpty k (toToml v)

protected def WorkspaceConfig.toToml (cfg : WorkspaceConfig) (t : Table := {}) : Table :=
  insertD `packages cfg.packagesDir defaultPackagesDir t

instance : ToToml WorkspaceConfig := ⟨(·.toToml)⟩

instance : ToToml BuildType := ⟨(toToml ·.toString)⟩
instance : ToToml Backend := ⟨(toToml ·.toString)⟩

def Toml.encodeLeanOptionValue (v : LeanOptionValue) : Value :=
  match v with
  | .ofString s => toToml s
  | .ofBool b => toToml b
  | .ofNat n => toToml n

instance : ToToml LeanOptionValue := ⟨encodeLeanOptionValue⟩

def Toml.encodeLeanOptions (opts : Array LeanOption) : Table :=
  opts.foldl (init := {}) fun vs ⟨k,v⟩ => vs.insert k (toToml v)

def LeanConfig.toToml (cfg : LeanConfig) (t : Table := {}) : Table :=
  insertD `buildType  cfg.buildType .release t
  |> insertD `backend cfg.backend .default
  |> insertSome `platformIndependent cfg.platformIndependent
  |>.insertUnless cfg.leanOptions.isEmpty `leanOptions
    (.table .missing <| encodeLeanOptions cfg.leanOptions)
  |>.insertUnless cfg.moreServerOptions.isEmpty `moreServerOptions
    (.table .missing <| encodeLeanOptions cfg.moreServerOptions)
  |> insertNotEmpty `moreLeanArgs cfg.moreLeanArgs
  |> insertNotEmpty `weakLeanArgs cfg.weakLeanArgs
  |> insertNotEmpty `moreLeancArgs cfg.moreLeancArgs
  |> insertNotEmpty `weakLeancArgs cfg.weakLeancArgs
  |> insertNotEmpty `moreLinkArgs cfg.moreLinkArgs
  |> insertNotEmpty `weakLinkArgs cfg.weakLinkArgs

instance : ToToml LeanConfig := ⟨(·.toToml)⟩

protected def PackageConfig.toToml (cfg : PackageConfig) (t : Table := {}) : Table :=
  t.insert `name (toToml cfg.name)
  |> insertD `precompileModules cfg.precompileModules false
  |> insertD `moreGlobalServerArgs cfg.moreGlobalServerArgs #[]
  |> insertD `srcDir cfg.srcDir "."
  |> insertD `buildDir cfg.buildDir defaultBuildDir
  |> insertD `leanLibDir cfg.leanLibDir defaultLeanLibDir
  |> insertD `nativeLibDir cfg.nativeLibDir defaultNativeLibDir
  |> insertD `binDir cfg.binDir defaultBinDir
  |> insertD `irDir cfg.irDir defaultIrDir
  |> insertSome `releaseRepo (cfg.releaseRepo <|> cfg.releaseRepo?)
  |> insertSome `buildArchive cfg.buildArchive? -- TODO: account for `buildArchive`
  |> insertD `preferReleaseBuild cfg.preferReleaseBuild false
  |> cfg.toWorkspaceConfig.toToml
  |> cfg.toLeanConfig.toToml

instance : ToToml PackageConfig := ⟨(·.toToml)⟩

instance : ToToml Glob := ⟨(toToml ·.toString)⟩

protected def LeanLibConfig.toToml (cfg : LeanLibConfig) (t : Table := {}) : Table :=
  t.insert `name (toToml cfg.name)
  |> insertD `srcDir cfg.srcDir "."
  |> insertD `roots cfg.roots #[cfg.name]
  |> insertD `globs cfg.globs (cfg.roots.map .one)
  |> insertD `libName cfg.libName (cfg.name.toString (escape := false))
  |> insertD `precompileModules cfg.precompileModules false
  |> insertD `defaultFacets cfg.defaultFacets #[LeanLib.leanArtsFacet]
  |> cfg.toLeanConfig.toToml

instance : ToToml LeanLibConfig := ⟨(·.toToml)⟩

protected def LeanExeConfig.toToml (cfg : LeanExeConfig) (t : Table  := {}) : Table :=
  t.insert `name (toToml cfg.name)
  |> insertD `srcDir cfg.srcDir "."
  |> insertD `root cfg.root cfg.name
  |> insertD `exeName cfg.exeName (cfg.name.toStringWithSep "-" (escape := false))
  |> insertD `supportInterpreter cfg.supportInterpreter false
  |> cfg.toLeanConfig.toToml

instance : ToToml LeanExeConfig := ⟨(·.toToml)⟩

protected def Dependency.toToml (dep : Dependency) (t : Table  := {}) : Table :=
  let t := t.insert `name (toToml dep.name)
  let t :=
    match dep.src with
    | .path dir => t.insert `path (toToml dir)
    | .git url rev subDir? =>
      t.insert `git url
      |> insertSome `rev rev
      |> insertSome `subDir subDir?
  t.insertUnless dep.opts.isEmpty `options <| .table .missing <|
    dep.opts.fold (init := {}) fun t k v => t.insert k (toToml v)

instance : ToToml Dependency := ⟨(·.toToml)⟩

protected def Package.mkTomlConfig (pkg : Package) (t : Table := {}) : Table :=
  pkg.config.toToml t
  |> insertNotEmpty `defaultTargets pkg.defaultTargets
  |> insertNotEmpty `require pkg.depConfigs
  |> insertNotEmpty `lean_lib pkg.leanLibConfigs.toArray
  |> insertNotEmpty `lean_exe pkg.leanExeConfigs.toArray

def translateConfig (cfg : LoadConfig) (lang : ConfigLang) (outFile : FilePath) : LogIO PUnit := do
  Lean.searchPathRef.set cfg.lakeEnv.leanSearchPath
  let (root, _) ← loadPackage "[root]" cfg
  let contents :=
    match lang with
    | .toml => ppTable root.mkTomlConfig
    | .lean => panic! "lean translation not yet implemented" -- TODO
  IO.FS.writeFile outFile contents
