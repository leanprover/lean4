module

import Lean.Runtime

/-!
Windows builds must load libuv 1.53.0 or newer, which includes the loopback TCP fix for #15807.
Run both compiled and interpreted so this checks the linked runtime, not package metadata.
-/

public def main : IO Unit := do
  let version := Lean.libUVVersion
  if System.Platform.isWindows && version < 0x013500 then
    throw <| IO.userError s!"Windows requires libuv >= 1.53.0; loaded {version >>> 16}.{(version >>> 8) &&& 255}.{version &&& 255}"
