/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lean.Data.Name
import Lean.Data.Options
import Lake.Config.Env
import Lake.Load.Manifest
import Lake.Util.FilePath

namespace Lake
open System Lean

/-- Context for loading a Lake configuration. -/
structure LoadConfig where
  /-- The Lake environment of the load process. -/
  lakeEnv : Lake.Env
  /--
  The CLI arguments Lake was run with.
  Used to perform a restart of Lake on a toolchain update.
  A value of `none` means that Lake is not restartable via the CLI.
  -/
  lakeArgs? : Option (Array String) := none
  /-- The absolute path to the root directory of the Lake workspace. -/
  wsDir : FilePath
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
  /-- A set of key-value Lake configuration options (i.e., `-K` settings). -/
  lakeOpts : NameMap String := {}
  /-- The Lean options with which to elaborate the configuration file. -/
  leanOpts : Options := {}
  /-- Whether Lake should re-elaborate configuration files instead of using cached OLeans. -/
  reconfigure : Bool := false
  /-- Whether to update dependencies when loading the workspace. -/
  updateDeps : Bool := false
  /--
  Whether to update the workspace's `lean-toolchain` when dependencies are updated.
  If `true` and a toolchain update occurs, Lake will need to be restarted.
  -/
  updateToolchain : Bool := true
  /-- The package's scope (e.g., in Reservoir). -/
  scope : String := ""
  /-- The URL to this package's Git remote (if any). -/
  remoteUrl : String := ""

/-- The package's Lake directory (for Lake temporary files). -/
@[inline] def LoadConfig.lakeDir (cfg : LoadConfig) : FilePath :=
  cfg.pkgDir / defaultLakeDir
