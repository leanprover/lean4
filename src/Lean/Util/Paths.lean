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

def initSrcSearchPath (pkgSearchPath : SearchPath := ∅) : IO SearchPath := do
  let srcSearchPath := (← IO.getEnv "LEAN_SRC_PATH")
    |>.map System.SearchPath.parse
    |>.getD []
  let srcPath := (← IO.appDir) / ".." / "src" / "lean"
  -- `lake/` should come first since on case-insensitive file systems, Lean thinks that `src/` also contains `Lake/`
  return srcSearchPath ++ pkgSearchPath ++ [srcPath / "lake", srcPath]

end Lean
