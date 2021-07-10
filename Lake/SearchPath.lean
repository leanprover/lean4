/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Util.Path

open System

namespace Lake

def getLeanHome? : IO (Option FilePath) := do
  let out ← IO.Process.output {
    cmd := "lean",
    args := #["--print-prefix"]
  }
  if out.exitCode == 0 then
    some <| FilePath.mk <| out.stdout.trim
  else
    none

def getLakeHome? : IO (Option FilePath) := do
  (← IO.appPath).parent.bind FilePath.parent

/--
  Initializes the search path the Lake executable
  uses when interpreting package configuration files.

  In order to use the Lean stdlib (e.g., `Init`),
  the executable needs the search path to include the directory
  with the stdlib's `.olean` files (e.g., from `<lean-home>/lib/lean`).
  In order to use Lake's modules as well, the search path also
  needs to include Lake's `.olean` files (e.g., from `build`).

  While this can be done by having the user augment `LEAN_PATH` with
  the necessary directories, Lake also intelligently derives an initial
  search path from the location of the `lean` executable and itself.

  It will assume that `lean` is located at `<lean-home>/bin/lean`
  with its `.olean` files at `<lean-home>/lib/lean` and that `lake`
  is at `<lake-home>/bin/lake` with its `.olean` files at `<lake-home>`.
  If this is correct, the user will not need to augment `LEAN_PATH`.
-/
def setupLeanSearchPath : IO Unit := do
  let mut sp : SearchPath := []
  if let some lakeHome ← getLakeHome? then
    sp := lakeHome :: sp
  if let some leanHome ← getLeanHome? then
    sp := leanHome / "lib" / "lean" :: sp
  sp ← Lean.addSearchPathFromEnv sp
  Lean.searchPathRef.set sp
