/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Util.NativeLib

open System
namespace Lake

/-- Standard path of `lean` in a Lean installation. -/
def leanExe (sysroot : FilePath) :=
  sysroot / "bin" / "lean" |>.withExtension FilePath.exeExtension

/-- Standard path of `leanc` in a Lean installation. -/
def leancExe (sysroot : FilePath) :=
  sysroot / "bin" / "leanc" |>.withExtension FilePath.exeExtension

/-- Standard path of `llvm-ar` in a Lean installation. -/
def leanArExe (sysroot : FilePath) :=
  sysroot / "bin" / "llvm-ar" |>.withExtension FilePath.exeExtension

/-- Standard path of `clang` in a Lean installation. -/
def leanCcExe (sysroot : FilePath) :=
  sysroot / "bin" / "clang" |>.withExtension FilePath.exeExtension

/-- Standard path of `libleanshared` in a Lean installation. -/
def leanSharedLib (sysroot : FilePath) :=
  let dir :=
    if Platform.isWindows then
      sysroot / "bin"
    else
      sysroot / "lib" / "lean"
  dir / "libleanshared" |>.withExtension sharedLibExt

/-- Path information about the local Lean installation. -/
structure LeanInstall where
  sysroot : FilePath
  githash : String
  srcDir := sysroot / "src" / "lean"
  leanLibDir := sysroot / "lib" / "lean"
  includeDir := sysroot / "include"
  systemLibDir := sysroot / "lib"
  binDir := sysroot / "bin"
  lean := leanExe sysroot
  leanc := leancExe sysroot
  sharedLib := leanSharedLib sysroot
  ar : FilePath
  cc : FilePath
  customCc : Bool
  deriving Inhabited, Repr

/--
A `SearchPath` including the Lean installation's shared library directories
(i.e., the system library and Lean library directories).
-/
def LeanInstall.sharedLibPath (self : LeanInstall) : SearchPath :=
  if Platform.isWindows then
    [self.binDir]
  else
    [self.leanLibDir, self.systemLibDir]

/-- The `LEAN_CC` of the Lean installation. -/
def LeanInstall.leanCc? (self : LeanInstall) : Option String :=
  if self.customCc then self.cc.toString else none

/-- Standard path of `lake` in a Lake installation. -/
def lakeExe (buildHome : FilePath) :=
  buildHome / "bin" / "lake" |>.withExtension FilePath.exeExtension

/-- Path information about the local Lake installation. -/
structure LakeInstall where
  home : FilePath
  srcDir := home
  binDir := home / "build" / "bin"
  libDir := home / "build" / "lib"
  lake := lakeExe <| home / "build"
  deriving Inhabited, Repr

/--
Try to find the sysroot of the given `lean` command (if it exists)
by calling `lean --print-prefix` and returning the path it prints.
Defaults to trying the `lean` in `PATH`.
-/
def findLeanSysroot? (lean := "lean") : BaseIO (Option FilePath) := do
  let act : IO _ := do
    let out ← IO.Process.output {
      cmd := lean,
      args := #["--print-prefix"]
    }
    if out.exitCode == 0 then
      pure <| some <| FilePath.mk <| out.stdout.trim
    else
      pure <| none
  act.catchExceptions fun _ => pure none

/--
Construct the `LeanInstall` object for the given Lean sysroot.

Does the following:
1. Invokes `lean` to find out its `githash`.
2. Finds the  `ar` and `cc` to use with Lean.
3. Computes the sub-paths of the Lean install.

For (1), if the invocation fails, `githash` is set to the empty string.

For (2), if `LEAN_AR` or `LEAN_CC` are defined, it uses those paths.
Otherwise, if Lean is packaged with an `llvm-ar` and/or `clang`, use them.
If not, use the `ar` and/or `cc` in the system's `PATH`. This last step is
needed because internal builds of Lean do not bundle these tools
(unlike user-facing releases).

We also track whether `LEAN_CC` was set to determine whether it should
be set in the future for `lake env`. This is because if `LEAN_CC` was not set,
it needs to remain not set for `leanc` to work.
Even setting it to the bundled compiler will break `leanc` -- see
[leanprover/lean4#1281](https://github.com/leanprover/lean4/issues/1281).

For (3), it assumes that the Lean installation is organized the normal way.
That is, with its binaries located in `<lean-sysroot>/bin`, its
Lean libraries in `<lean-sysroot>/lib/lean`, and its system libraries in
`<lean-sysroot>/lib`.
-/
def LeanInstall.get (sysroot : FilePath) : BaseIO LeanInstall := do
  let (cc, customCc) ← findCc
  return {
    sysroot,
    githash := ← getGithash
    ar := ← findAr
    cc, customCc
  }
where
  getGithash := do
    let act : IO _ := do
      let out ← IO.Process.output {
        cmd := leanExe sysroot |>.toString,
        args := #["--githash"]
      }
      pure <| out.stdout.trim
    act.catchExceptions fun _ => pure ""
  findAr := do
    if let some ar ← IO.getEnv "LEAN_AR" then
      return ar
    else
      let ar := leanArExe sysroot
      if (← ar.pathExists) then pure ar else pure "ar"
  findCc := do
    if let some cc ← IO.getEnv "LEAN_CC" then
      return (FilePath.mk cc, true)
    else
      let cc := leanCcExe sysroot
      let cc := if (← cc.pathExists) then cc else "cc"
      return (cc, false)

/--
Try to find the installation of the given `lean` command
by calling `findLeanCmdHome?`. See `LeanInstall.get` for how it assumes the
Lean install is organized.
-/
def findLeanCmdInstall? (lean := "lean") : BaseIO (Option LeanInstall) :=
  OptionT.run do LeanInstall.get (← findLeanSysroot? lean)

/--
Check if Lake's executable is co-located with Lean, and, if so,
try to return their joint home by assuming they are both located at `<home>/bin`.
-/
def findLakeLeanJointHome? : BaseIO (Option FilePath) := do
  if let Except.ok appPath ← IO.appPath.toBaseIO then
    if let some appDir := appPath.parent then
      let leanExe := appDir / "lean" |>.withExtension FilePath.exeExtension
      if (← leanExe.pathExists) then
        return appDir.parent
  return none

/--
Try to get Lake's home by assuming
the executable is located at `<lake-home>/build/bin/lake`.
-/
def lakePackageHome? (lake : FilePath) : Option FilePath := do
  (← (← lake.parent).parent).parent

/--
Try to find Lean's installation by first checking the
`LEAN_SYSROOT` environment variable and then by trying `findLeanCmdHome?`.
See `LeanInstall.get` for how it assumes the Lean install is organized.
-/
def findLeanInstall? : BaseIO (Option LeanInstall) := do
  if let some sysroot ← IO.getEnv "LEAN_SYSROOT" then
    return some <| ← LeanInstall.get sysroot
  if let some sysroot ← findLeanSysroot? then
    return some <| ← LeanInstall.get sysroot
  return none

/--
Try to find Lake's installation by
first checking the `LAKE_HOME` environment variable
and then by trying the `lakePackageHome?` of the running executable.

It assumes that the Lake installation is organized the same way it is built.
That is, with its binary located at `<lake-home>/build/bin/lake` and its static
library and `.olean` files in `<lake-home>/build/lib`, and its source files
located directly in `<lake-home>`.
-/
def findLakeInstall? : BaseIO (Option LakeInstall) := do
  if let some home ← IO.getEnv "LAKE_HOME" then
    return some {home}
  if let Except.ok lake ← IO.appPath.toBaseIO then
    if let some home := lakePackageHome? lake then
      return some {home, lake}
  return none

/--
Try to get Lake's install path by first trying `findLakeLeanHome?`
then by running `findLeanInstall?` and `findLakeInstall?`.

If Lake is co-located with `lean` (i.e., there is `lean` executable
in the same directory as itself), it will assume it was installed with
Lean and that both Lake's and Lean's files are all located their shared
sysroot.
In particular, their binaries are located in `<sysroot>/bin`,
their Lean libraries in `<sysroot>/lib/lean`,
Lean's source files in `<sysroot>/src/lean`,
and Lake's source files in `<sysroot>/src/lean/lake`.
-/
def findInstall? : BaseIO (Option LeanInstall × Option LakeInstall) := do
  if let some home ← findLakeLeanJointHome? then
    let lean ← LeanInstall.get home
    return (
      some lean,
      some {
        home,
        srcDir := lean.srcDir / "lake",
        binDir := lean.binDir,
        libDir := lean.leanLibDir,
        lake := lakeExe home
      }
    )
  else
    return (← findLeanInstall?, ← findLakeInstall?)
