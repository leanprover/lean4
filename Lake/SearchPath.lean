/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Util.Path

open System
namespace Lake

/--
  Try to find the home of Lean by calling
  `lean --print-prefix` and returning the path it prints.
-/
def getLeanHome? : IO (Option FilePath) := do
  let out ← IO.Process.output {
    cmd := "lean",
    args := #["--print-prefix"]
  }
  if out.exitCode == 0 then
    some <| FilePath.mk <| out.stdout.trim
  else
    none

/--
  Try to get Lake's home by assuming
  this executable is located at `<lake-home>/bin/lake`.
-/
def getLakeHome? : IO (Option FilePath) := do
  (← IO.appPath).parent.bind FilePath.parent


/--
  Check if Lake's executable is co-located with Lean, and, if so,
  try to return their joint home by assuming they are located at `<app-home>/bin`.
-/
def getAppHome? : IO (Option FilePath) := do
  let appPath ← IO.appPath
  if let some appDir := appPath.parent then
    let leanExe := appDir / "lean" |>.withExtension FilePath.exeExtension
    if (← leanExe.pathExists) then
      return appDir.parent
  return none

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

  If Lake is co-located with `lean` (i.e., there is `lean` executable
  in the same directory as itself), it will assume it was installed with
  Lean and that both Lean and Lake are located in `<lean-home>/bin` with
  Lean's `.olean` files at `<lean-home/lib/lean` and Lake's at `.olean` files
  at `<lean-home/lib/lake`.

  Otherwise, it will run `lean --print-prefix` to find Lean's home and
  assume that its `.olean` files are at `<lean-home>/lib/lean` and that `lake`
  is at `<lake-home>/bin/lake` with its `.olean` files at `<lake-home>`.
  If this is correct, the user will not need to augment `LEAN_PATH`.
-/
def setupLeanSearchPath : IO Unit := do
  let mut sp : SearchPath := []
  if let some appHome ← getAppHome? then
    -- we are co-located with Lean
    let libDir := appHome / "lib"
    sp := libDir / "lean" :: libDir / "lake" :: sp
  else
    -- we are a custom installation
    if let some lakeHome ← getLakeHome? then
      sp := lakeHome :: sp
    if let some leanHome ← getLeanHome? then
      sp := leanHome / "lib" / "lean" :: sp
  sp ← Lean.addSearchPathFromEnv sp
  Lean.searchPathRef.set sp
