/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lake.Config.Env
public import Lake.Load.Manifest
public import Lake.Util.FilePath

set_option doc.verso true

open System Lean

namespace Lake

/-- Context for loading a Lake configuration. -/
public structure LoadConfig where
  /-- The Lake environment of the load process. -/
  lakeEnv : Lake.Env
  /--
  The CLI arguments Lake was run with.
  Used to perform a restart of Lake on a toolchain update.
  A value of {lean}`none` means that Lake is not restartable via the CLI.
  -/
  lakeArgs? : Option (Array String) := none
  /-- The absolute path to the root directory of the Lake workspace. -/
  wsDir : FilePath
  /-- The index of the package in the workspace. Used to disambiguate packages with the same name. -/
  pkgIdx : Nat := 0
  /--
  The assigned name of the package.
  If {lean}`Name.anonymous`, the package's own name will be used.
  -/
  pkgName : Name := .anonymous
  /-- The loaded package's directory (relative to the workspace directory). -/
  relPkgDir : FilePath := "."
  /-- The absolute path to the loaded package's directory. -/
  pkgDir : FilePath := wsDir / relPkgDir
  /-- The package's Lake configuration file (relative to its directory). -/
  relConfigFile : FilePath := defaultConfigFile
    /-- The full path to the loaded package's Lake configuration file. -/
  configFile : FilePath := pkgDir / relConfigFile
  /-- Additional package overrides for this workspace load. -/
  packageOverrides : Array PackageEntry := #[]
  /-- A set of key-value Lake configuration options (i.e., {lit}`-K` settings). -/
  lakeOpts : NameMap String := {}
  /-- The Lean options with which to elaborate the configuration file. -/
  leanOpts : Options := {}
  /-- Whether Lake should re-elaborate configuration files instead of using cached OLeans. -/
  reconfigure : Bool := false
  /-- Whether to update dependencies when loading the workspace. -/
  updateDeps : Bool := false
  /--
  Whether to update the workspace's {lit}`lean-toolchain` when dependencies are updated.
  If {lean}`true` and a toolchain update occurs, Lake will need to be restarted.
  -/
  updateToolchain : Bool := true
  /-- The package's scope (e.g., in Reservoir). -/
  scope : String := ""
  /-- The URL to this package's Git remote (if any). -/
  remoteUrl : String := ""

namespace LoadConfig

/-- The package's Lake directory (for Lake temporary files). -/
@[inline] public def lakeDir (cfg : LoadConfig) : FilePath :=
  cfg.pkgDir / defaultLakeDir
