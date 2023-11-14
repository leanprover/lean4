def Lean.determineLakePath : IO System.FilePath := do
  if let some lakePath ← IO.getEnv "LAKE" then
    return System.FilePath.mk lakePath

  let sysroot? ← IO.getEnv "LEAN_SYSROOT"
  let lakePath ← match sysroot? with
    | some sysroot => pure <| System.FilePath.mk sysroot / "bin" / "lake"
    | none         => pure <| (← IO.appDir) / "lake"
