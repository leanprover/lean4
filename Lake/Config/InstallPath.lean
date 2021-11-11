/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
open System
namespace Lake

/-- The shared library file extension for the `Platform`. -/
def sharedLibExt : String :=
  if Platform.isWindows then "dll"
  else if Platform.isOSX  then "dylib"
  else "so"

/-- Path information about the local Lean installation. -/
structure LeanInstall where
  home : FilePath
  binDir := home / "bin"
  libDir := home / "lib" / "lean"
  oleanDir := libDir
  includeDir := home / "include"
  lean := binDir / "lean" |>.withExtension FilePath.exeExtension
  leanc := binDir / "leanc" |>.withExtension FilePath.exeExtension
  sharedLib := (if Platform.isWindows then binDir else libDir) / "libleanshared" |>.withExtension sharedLibExt
  deriving Inhabited, Repr

/-- Path information about the local Lake installation. -/
structure LakeInstall where
  home : FilePath
  binDir := home / "bin"
  libDir := home / "lib"
  oleanDir := libDir
  lake := binDir / "lake" |>.withExtension FilePath.exeExtension
  deriving Inhabited, Repr

/--
  Try to find the home of the given `lean` command (if it exists)
  by calling `lean --print-prefix` and returning the path it prints.
  Defaults to trying the `lean` in `PATH`.
-/
def findLeanCmdHome? (lean := "lean") : IO (Option FilePath) := do
  let out ← IO.Process.output {
    cmd := lean,
    args := #["--print-prefix"]
  }
  if out.exitCode == 0 then
    some <| FilePath.mk <| out.stdout.trim
  else
    none

/--
  Try to find the installation of the given `lean` command
  by calling `findLeanCmdHome?`.

  It assumes that the Lean installation is setup the normal way.
  That is, with its binaries located in `<lean-home>/bin` and its
  libraries and `.olean` files located in `<lean-home>/lib/lean`.
-/
def findLeanCmdInstall? (lean := "lean"): IO (Option LeanInstall) := do
  (← findLeanCmdHome? lean).map fun home => {home}

/--
  Try to get Lake's home by assuming
  this executable is located at `<lake-home>/bin/lake`.
-/
def findLakeBuildHome? : IO (Option FilePath) := do
  (← IO.appPath).parent.bind FilePath.parent

/--
  Check if Lake's executable is co-located with Lean, and, if so,
  try to return their joint home by assuming they are both located at `<home>/bin`.
-/
def findLakeLeanJointHome? : IO (Option FilePath) := do
  let appPath ← IO.appPath
  if let some appDir := appPath.parent then
    let leanExe := appDir / "lean" |>.withExtension FilePath.exeExtension
    if (← leanExe.pathExists) then
      return appDir.parent
  return none

/--
  Try to find Lean's installation by
  first checking the `LEAN_SYSROOT` environment variable
  and then by trying `findLeanCmdHome?`.

  It assumes that the Lean installation is setup the normal way.
  That is, with its binaries located in `<lean-home>/bin` and its
  libraries and `.olean` files located in `<lean-home>/lib/lean`.
-/
def findLeanInstall? : IO (Option LeanInstall) := do
  if let some home ← IO.getEnv "LEAN_SYSROOT" then
    return some {home}
  if let some home ← findLeanCmdHome? then
    return some {home}
  return none

/--
  Try to find Lake's installation by
  first checking the `LAKE_HOME` environment variable
  and then by trying `findLakeBuildHome?`.

  It assumes that the Lake installation is setup the same way it is built.
  That is, with its binary located at `<lake-home>/bin/lake` and its static
  library and `.olean` files in `<lake-home>/lib`.
-/
def findLakeInstall? : IO (Option LakeInstall) := do
  if let some home ← IO.getEnv "LAKE_HOME" then
    return some {home}
  if let some home ← findLakeBuildHome? then
    return some {home}
  return none

/--
  Try to get Lake's install path by first trying `findLakeLeanHome?`
  then by running `findLeanInstall?` and `findLakeInstall?`.

  If Lake is co-located with `lean` (i.e., there is `lean` executable
  in the same directory as itself), it will assume it was installed with
  Lean and their binaries are located in `<lean-home>/bin` with
  Lean's libraries and `.olean` files at `<lean-home>/lib/lean` and
  Lake's static library and `.olean` files at `<lean-home>/lib/lean`.
-/
def findInstall? : IO (Option LeanInstall × Option LakeInstall) := do
  if let some home ← findLakeLeanJointHome? then
    return (some {home}, some {home, libDir := home / "lib" / "lean"})
  else
    return (← findLeanInstall?, ← findLakeInstall?)
