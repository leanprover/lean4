/-
Copyright (c) 2021 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Sebastian Ullrich
-/
import Lean.Data.Json
import Lean.Util.Path

/-! Communicating Lean module / search paths between processes -/

namespace Lean

open System

structure LeanPaths where
  oleanPath : SearchPath
  srcPath   : SearchPath
  deriving ToJson, FromJson

structure ModulePaths where
  module : Name
  olean? : Option FilePath
  src? : Option FilePath
  deriving ToJson, FromJson

end Lean
