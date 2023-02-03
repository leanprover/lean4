/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Util.NativeLib
import Lake.Config.InstallPath

open System

namespace Lake

/-- The detected Lake environment. -/
structure Env where
  lake : LakeInstall
  lean : LeanInstall
  leanPath : SearchPath
  leanSrcPath : SearchPath
  sharedLibPath : SearchPath
  deriving Inhabited, Repr

namespace Env

/-- Compute an `Lake.Env` object from the given installs and set environment variables. -/
def compute (lake : LakeInstall) (lean : LeanInstall) : BaseIO Env :=
  return {
    lake, lean
    leanPath := ← getSearchPath "LEAN_PATH",
    leanSrcPath := ← getSearchPath "LEAN_SRC_PATH",
    sharedLibPath := ← getSearchPath sharedLibPathEnvVar
  }

/-- Environment variable settings based only on the given Lean and Lake installations. -/
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
  env.installVars ++ #[
    ("LEAN_PATH", some env.leanPath.toString),
    ("LEAN_SRC_PATH", some env.leanSrcPath.toString),
    (sharedLibPathEnvVar, some env.sharedLibPath.toString)
  ]

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
