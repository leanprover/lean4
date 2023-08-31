/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Util.NativeLib
import Lake.Config.InstallPath

open System

/-! # Lake's Environment
Definitions related to a Lake environment.
A Lake environment is computed on Lake's startup from
user-specified CLI options and the process environment.
-/

namespace Lake

/-- A Lake environment. -/
structure Env where
  /-- The Lake installation of the environment. -/
  lake : LakeInstall
  /-- The Lean installation of the environment. -/
  lean : LeanInstall
  /-- The initial Lean library search path of the environment (i.e., `LEAN_PATH`). -/
  initLeanPath : SearchPath
  /-- The initial Lean source search path of the environment (i.e., `LEAN_SRC_PATH`). -/
  initLeanSrcPath : SearchPath
  /-- The initial shared library search path of the environment. -/
  initSharedLibPath : SearchPath
  /-- The initial binary search path of the environment (i.e., `PATH`). -/
  initPath : SearchPath
  deriving Inhabited, Repr

namespace Env

/-- Compute an `Lake.Env` object from the given installs and set environment variables. -/
def compute (lake : LakeInstall) (lean : LeanInstall) : BaseIO Env :=
  return {
    lake, lean,
    initLeanPath := ← getSearchPath "LEAN_PATH",
    initLeanSrcPath := ← getSearchPath "LEAN_SRC_PATH",
    initSharedLibPath := ← getSearchPath sharedLibPathEnvVar,
    initPath := ← getSearchPath "PATH"
  }

/--
The Lean library search path of the environment (i.e., `LEAN_PATH`).
Combines the initial path of the environment with that of the Lake installation.
-/
def path (env : Env) : SearchPath :=
  if env.lake.binDir = env.lean.binDir then
    env.lean.binDir :: env.initPath
  else
    env.lake.binDir :: env.lean.binDir :: env.initPath

/-
We include Lake's installation in the cases below to ensure that the
Lake being used to build is available to the environment (and thus, e.g.,
the Lean server). Otherwise, it may fall back on whatever the default Lake
instance is.
-/

/--
The Lean library search path of the environment (i.e., `LEAN_PATH`).
Combines the initial path of the environment with that of the Lake installation.
-/
def leanPath (env : Env) : SearchPath :=
  env.lake.libDir :: env.initLeanPath

/--
The Lean source search path of the environment (i.e., `LEAN_SRC_PATH`).
Combines the initial path of the environment with that of the Lake abd Lean
installations.
-/
def leanSrcPath (env : Env) : SearchPath :=
  env.lake.srcDir :: env.initLeanSrcPath

/--
The shared library search path of the environment.
Combines the initial path of the environment with that of the Lean installation.
-/
def sharedLibPath (env : Env) : SearchPath :=
  env.lean.sharedLibPath ++ env.initSharedLibPath

/-- Environment variable settings based only on the Lean and Lake installations. -/
def installVars (env : Env) : Array (String × Option String)  :=
  #[
    ("LAKE", env.lake.lake.toString),
    ("LAKE_HOME", env.lake.home.toString),
    ("LEAN_SYSROOT", env.lean.sysroot.toString),
    ("LEAN_AR", env.lean.ar.toString),
    ("LEAN_CC", env.lean.leanCc?)
  ]

/-- Environment variable settings for the `Lake.Env`. -/
def vars (env : Env) : Array (String × Option String)  :=
  let vars := env.installVars ++ #[
    ("LEAN_PATH", some env.leanPath.toString),
    ("LEAN_SRC_PATH", some env.leanSrcPath.toString),
    ("PATH", some env.path.toString)
  ]
  if Platform.isWindows then
    vars
  else
    vars.push (sharedLibPathEnvVar, some <| env.sharedLibPath.toString)

/--
The default search path the Lake executable
uses when interpreting package configuration files.

In order to use the Lean stdlib (e.g., `Init`),
the executable needs the search path to include the directory
with the stdlib's `.olean` files (e.g., from `<lean-sysroot>/lib/lean`).
In order to use Lake's modules as well, the search path also
needs to include Lake's `.olean` files (e.g., from `build`).

While this can be done by having the user augment `LEAN_PATH` with
the necessary directories, Lake also intelligently augments the initial
search path with the `.olean` directories of the provided Lean and Lake
installations.

See `findInstall?` for more information on how Lake determines those
directories. If everything is configured as expected, the user will not
need to augment `LEAN_PATH`. Otherwise, they will need to provide Lake
with more information (either through `LEAN_PATH` or through other options).
-/
def leanSearchPath (env : Lake.Env) : SearchPath :=
  env.lake.libDir :: env.lean.leanLibDir :: env.leanPath
