/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Util.NativeLib
import Lake.Config.Defaults

open System
namespace Lake

/-- Convert the string value of an environment variable to a boolean. -/
def envToBool? (o : String) : Option Bool :=
  if ["y", "yes", "t", "true", "on", "1"].contains o.toLower then true
  else if ["n", "no", "f", "false", "off", "0"].contains o.toLower then false
  else none

/-! ## Data Structures -/

/-- Information about the local Elan setup. -/
structure ElanInstall where
  home : FilePath
  elan : FilePath
  binDir := home / "bin"
  toolchainsDir := home / "toolchains"
  deriving Inhabited, Repr

/-- Standard path of `lean` in a Lean installation. -/
def leanExe (sysroot : FilePath) :=
  sysroot / "bin" / "lean" |>.addExtension FilePath.exeExtension

/-- Standard path of `leanc` in a Lean installation. -/
def leancExe (sysroot : FilePath) :=
  sysroot / "bin" / "leanc" |>.addExtension FilePath.exeExtension

/-- Standard path of `llvm-ar` in a Lean installation. -/
def leanArExe (sysroot : FilePath) :=
  sysroot / "bin" / "llvm-ar" |>.addExtension FilePath.exeExtension

/-- Standard path of `clang` in a Lean installation. -/
def leanCcExe (sysroot : FilePath) :=
  sysroot / "bin" / "clang" |>.addExtension FilePath.exeExtension

/-- Standard path of shared libraries in a Lean installation. -/
def leanSharedLibDir (sysroot : FilePath) :=
  if Platform.isWindows then
    sysroot / "bin"
  else
    sysroot / "lib" / "lean"

/-- `libleanshared` file name. -/
def leanSharedLib  :=
  FilePath.addExtension "libleanshared" sharedLibExt

/-- `Init` shared library file name. -/
def initSharedLib : FilePath :=
  FilePath.addExtension "libInit_shared" sharedLibExt

/-- Path information about the local Lean installation. -/
structure LeanInstall where
  sysroot : FilePath
  githash : String := ""
  srcDir := sysroot / "src" / "lean"
  leanLibDir := sysroot / "lib" / "lean"
  includeDir := sysroot / "include"
  systemLibDir := sysroot / "lib"
  binDir := sysroot / "bin"
  lean := leanExe sysroot
  leanc := leancExe sysroot
  sharedLib := leanSharedLibDir sysroot / leanSharedLib
  initSharedLib := leanSharedLibDir sysroot / initSharedLib
  ar : FilePath := "ar"
  cc : FilePath := "cc"
  customCc : Bool := false
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

/-- Lake executable file name. -/
def lakeExe : FilePath :=
  FilePath.addExtension "lake" FilePath.exeExtension

/-- Path information about the local Lake installation. -/
structure LakeInstall where
  home : FilePath
  srcDir := home
  binDir := home / defaultBuildDir / defaultBinDir
  libDir := home / defaultBuildDir / defaultLeanLibDir
  lake := binDir / lakeExe
  deriving Inhabited, Repr

/-- Construct a Lake installation co-located with the specified Lean installation. -/
def LakeInstall.ofLean (lean : LeanInstall) : LakeInstall where
  home := lean.sysroot
  srcDir := lean.srcDir / "lake"
  binDir := lean.binDir
  libDir := lean.leanLibDir
  lake := lean.binDir / lakeExe

/-! ## Detection Functions -/

/--
Attempt to detect an Elan installation by checking the `ELAN` and `ELAN_HOME`
environment variables. If `ELAN` is set but empty, Elan is considered disabled.
-/
def findElanInstall? : BaseIO (Option ElanInstall) := do
  if let some home ← IO.getEnv "ELAN_HOME" then
    let elan := (← IO.getEnv "ELAN").getD "elan"
    if elan.trim.isEmpty then
      return none
    else
      return some {elan, home}
  return none

/--
Attempt to find the sysroot of the given `lean` command (if it exists)
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
1. Find `lean`'s githash.
2. Finds the  `ar` and `cc` to use with Lean.
3. Computes the sub-paths of the Lean install.

For (1), If `lake` is not-collocated with `lean`, invoke `lean --githash`;
otherwise, use Lake's `Lean.githash`. If the invocation fails, `githash` is
set to the empty string.

For (2), if `LEAN_AR` or `LEAN_CC` are defined, it uses those paths.
Otherwise, if Lean is packaged with an `llvm-ar` and/or `clang`, use them.
If not, use the `ar` and/or `cc` from the `AR` / `CC` environment variables
or the system's `PATH`. This last step is needed because internal builds of
Lean do not bundle these tools (unlike user-facing releases).

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
def LeanInstall.get (sysroot : FilePath) (collocated : Bool := false) : BaseIO LeanInstall := do
  let githash ← do
    if collocated then
      pure Lean.githash
    else
      -- Remark: This is expensive (at least on Windows), so try to avoid it.
      getGithash
  let ar ← findAr
  let (cc, customCc) ← findCc
  return {sysroot, githash, ar, cc, customCc}
where
  getGithash := do
    EIO.catchExceptions (h := fun _ => pure "") do
      let out ← IO.Process.output {
        cmd := leanExe sysroot |>.toString,
        args := #["--githash"]
      }
      pure <| out.stdout.trim
  findAr := do
    if let some ar ← IO.getEnv "LEAN_AR" then
      return FilePath.mk ar
    else
      let ar := leanArExe sysroot
      if (← ar.pathExists) then
        return ar
      else if let some ar ← IO.getEnv "AR" then
        return ar
      else
        return "ar"
  findCc := do
    if let some cc ← IO.getEnv "LEAN_CC" then
      return (FilePath.mk cc, true)
    else
      let cc := leanCcExe sysroot
      let cc ←
        if (← cc.pathExists) then
          pure cc
        else if let some cc ← IO.getEnv "CC" then
          pure cc
        else
          pure "cc"
      return (cc, false)

/--
Attempt to detect the installation of the given `lean` command
by calling `findLeanSysroot?`. See `LeanInstall.get` for how it assumes the
Lean install is organized.
-/
def findLeanCmdInstall? (lean := "lean") : BaseIO (Option LeanInstall) :=
  OptionT.run do LeanInstall.get (← findLeanSysroot? lean)

/--
Check if the running Lake's executable is co-located with Lean, and, if so,
try to return their joint home by assuming they are both located at `<home>/bin`.
-/
def findLakeLeanJointHome? : BaseIO (Option FilePath) := do
  if let .ok appPath ← IO.appPath.toBaseIO then
    if let some appDir := appPath.parent then
      let leanExe := appDir / "lean" |>.addExtension FilePath.exeExtension
      if (← leanExe.pathExists) then
        return appDir.parent
  return none

/--
Get the root of Lake's installation by assuming the executable
is located at `<lake-home>/.lake/build/bin/lake`.
-/
def lakeBuildHome? (lake : FilePath) : Option FilePath := do
  (← (← (← lake.parent).parent).parent).parent

/--
Heuristically validate that `getLakeBuildHome?` is a proper Lake installation
by check for `Lake.olean` in the installation's `lib` directory.
-/
def getLakeInstall? (lake : FilePath) : BaseIO (Option LakeInstall) := do
  let some home := lakeBuildHome? lake | return none
  let lake : LakeInstall := {home, lake}
  if (← lake.libDir / "Lake.olean" |>.pathExists) then
    return lake
  return none

/--
Attempt to detect Lean's installation by using the `LEAN` and `LEAN_SYSROOT`
environment variables.

If `LEAN_SYSROOT` is set, use it. Otherwise, check `LEAN` for the `lean`
executable. If `LEAN` is set but empty, Lean will be considered disabled.
Otherwise, Lean's location will be determined by trying `findLeanSysroot?`
using value of `LEAN` or, if unset, the `lean` in `PATH`.

See `LeanInstall.get` for how it assumes the Lean install is organized.
-/
def findLeanInstall? : BaseIO (Option LeanInstall) := do
  if let some sysroot ← IO.getEnv "LEAN_SYSROOT" then
    return some <| ← LeanInstall.get sysroot
  let lean ← do
    if let some lean ← IO.getEnv "LEAN" then
      if lean.trim.isEmpty then
        return none
      else
        pure lean
    else
      pure "lean"
  if let some sysroot ← findLeanSysroot? lean then
    return some <| ← LeanInstall.get sysroot
  return none

/--
Attempt to detect Lake's installation by first checking the `lakeBuildHome?`
of the running executable, then trying the `LAKE_HOME` environment variable.

It assumes that the Lake installation is organized the same way it is built.
That is, with its binary located at `<lake-home>/.lake/build/bin/lake` and its
static library and `.olean` files in `<lake-home>/.lake/build/lib`, and
its source files located directly in `<lake-home>`.
-/
def findLakeInstall? : BaseIO (Option LakeInstall) := do
  if let Except.ok lake ← IO.appPath.toBaseIO then
    if let some lake ← getLakeInstall? lake then
      return lake
  if let some home ← IO.getEnv "LAKE_HOME" then
    return some {home}
  return none

/--
Attempt to automatically detect an Elan, Lake, and Lean installation.

First, it calls `findElanInstall?` to detect a Elan installation.
Then it attempts to detect if Lake and Lean are part of a single installation
where the `lake` executable is co-located with the `lean` executable (i.e., they
are in the same directory). If Lean and Lake are not co-located, Lake will
attempt  to find the their installations separately by calling
`findLeanInstall?` and `findLakeInstall?`. Setting `LAKE_OVERRIDE_LEAN` to true
will force Lake to use `findLeanInstall?` even if co-located.

When co-located, Lake will assume that Lean and Lake's binaries are located in
`<sysroot>/bin`, their Lean libraries  in `<sysroot>/lib/lean`, Lean's source files
in `<sysroot>/src/lean`, and Lake's source files in `<sysroot>/src/lean/lake`,
following the pattern of a regular Lean toolchain.
-/
def findInstall? : BaseIO (Option ElanInstall × Option LeanInstall × Option LakeInstall) := do
  let elan? ← findElanInstall?
  if let some sysroot ← findLakeLeanJointHome? then
    if (← IO.getEnv "LAKE_OVERRIDE_LEAN").bind envToBool? |>.getD false then
      let lake := LakeInstall.ofLean {sysroot}
      return (elan?, ← findLeanInstall?, lake)
    else
      let lean ← LeanInstall.get sysroot (collocated := true)
      let lake := LakeInstall.ofLean lean
      return (elan?, lean, lake)
  else
    return (elan?, ← findLeanInstall?, ← findLakeInstall?)
