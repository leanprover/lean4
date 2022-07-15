/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Data.Name
import Lake.Config.Env

namespace Lake
open System Lean

/-- Context for loading a Lake configuration. -/
structure LoadConfig where
  env : Lake.Env
  rootDir : FilePath
  configFile : FilePath
  options : NameMap String

/-- The default name of the Lake configuration file (i.e., `lakefile.lean`). -/
def defaultConfigFile : FilePath := "lakefile.lean"
