/-
Copyright (c) 2021 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Sebastian Ullrich
-/
import Lean.Data.Json
import Lean.Util.Path

/-! Communicating Lean search paths between processes -/

namespace Lean

open System

structure LeanPaths where
  oleanPath       : SearchPath
  srcPath         : SearchPath
  loadDynlibPaths : Array FilePath := #[]
  deriving ToJson, FromJson

def initSrcSearchPath (_leanSysroot : FilePath) (sp : SearchPath := ∅) : IO SearchPath := do
  let srcSearchPath :=
    if let some p := (← IO.getEnv "LEAN_SRC_PATH") then
      System.SearchPath.parse p
    else []
  let srcPath := (← IO.appDir) / ".." / "src" / "lean"
  -- `lake/` should come first since on case-insensitive file systems, Lean thinks that `src/` also contains `Lake/`
  return srcSearchPath ++ sp ++ [srcPath / "lake", srcPath]

end Lean
