/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Sebastian Ullrich
-/

def Lean.determineLakePath : IO System.FilePath := do
  if let some lakePath ← IO.getEnv "LAKE" then
    return System.FilePath.mk lakePath

  let sysroot? ← IO.getEnv "LEAN_SYSROOT"
  let lakePath ← match sysroot? with
    | some sysroot => pure <| System.FilePath.mk sysroot / "bin" / "lake"
    | none         => pure <| (← IO.appDir) / "lake"
