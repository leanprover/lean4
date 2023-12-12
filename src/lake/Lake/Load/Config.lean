/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Data.Name
import Lean.Data.Options
import Lake.Config.Env
import Lake.Util.Log

namespace Lake
open System Lean

/-- `elan` toolchain file name -/
def toolchainFileName : FilePath := "lean-toolchain"

/-- The default name of the Lake configuration file (i.e., `lakefile.lean`). -/
def defaultConfigFile : FilePath := "lakefile.lean"

/-- The default name of the Lake manifest file (i.e., `lake-manifest.json`). -/
def defaultManifestFile := "lake-manifest.json"

/-- Context for loading a Lake configuration. -/
structure LoadConfig where
  /-- The Lake environment of the load process. -/
  env : Lake.Env
  /-- The root directory of the loaded package (and its workspace). -/
  rootDir : FilePath
  /-- The Lean file with the package's Lake configuration (e.g., `lakefile.lean`) -/
  configFile : FilePath := rootDir / defaultConfigFile
  /-- A set of key-value Lake configuration options (i.e., `-K` settings). -/
  configOpts : NameMap String := {}
  /-- The Lean options with which to elaborate the configuration file. -/
  leanOpts : Options := {}
  /-- If true, Lake will elaborate configuration files instead of using OLeans. -/
  reconfigure : Bool := false
