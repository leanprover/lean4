/-
Copyright (c) 2021 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Sebastian Ullrich
-/
prelude
import Lean.Data.Json
import Lean.Util.Path

/-! Communicating Lean search paths between processes -/

namespace Lean

open System

structure LeanPaths where
  oleanPath       : SearchPath
  srcPath         : SearchPath
  loadDynlibPaths : Array FilePath := #[]
  pluginPaths     : Array FilePath := #[]
  deriving ToJson, FromJson

end Lean
