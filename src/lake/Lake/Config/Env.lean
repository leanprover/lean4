/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Util.Name
import Lake.Util.NativeLib
import Lake.Config.InstallPath

open System Lean

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
  /-- The Elan installation (if any) of the environment. -/
  elan? : Option ElanInstall
  /-- A name-to-URL mapping of URL overwrites for the named packages. -/
  pkgUrlMap : NameMap String
  /-- The initial Elan toolchain of the environment (i.e., `ELAN_TOOLCHAIN`). -/
  initToolchain : String
  /-- The initial Lean library search path of the environment (i.e., `LEAN_PATH`). -/
  initLeanPath : SearchPath
  /-- The initial Lean source search path of the environment (i.e., `LEAN_SRC_PATH`). -/
  initLeanSrcPath : SearchPath
  /-- The initial shared library search path of the environment. -/
  initSharedLibPath : SearchPath
  /-- The initial binary search path of the environment (i.e., `PATH`). -/
  initPath : SearchPath
  deriving Inhabited

namespace Env

/-- Compute an `Lake.Env` object from the given installs and set environment variables. -/
def compute (lake : LakeInstall) (lean : LeanInstall) (elan? : Option ElanInstall) : EIO String Env :=
  return {
    lake, lean, elan?,
    pkgUrlMap := ← computePkgUrlMap
    initToolchain := (← IO.getEnv "ELAN_TOOLCHAIN").getD ""
    initLeanPath := ← getSearchPath "LEAN_PATH",
    initLeanSrcPath := ← getSearchPath "LEAN_SRC_PATH",
    initSharedLibPath := ← getSearchPath sharedLibPathEnvVar,
    initPath := ← getSearchPath "PATH"
  }
where
  computePkgUrlMap := do
    let some urlMapStr ← IO.getEnv "LAKE_PKG_URL_MAP" | return {}
    match Json.parse urlMapStr |>.bind fromJson? with
    | .ok urlMap => return urlMap
    | .error e => throw s!"'LAKE_PKG_URL_MAP' has invalid JSON: {e}"

/--
The preferred toolchain of the environment. May be empty.
Tries `env.initToolchain` first and then Lake's `Lean.toolchain`.
-/
def toolchain (env : Env) : String :=
  if env.initToolchain.isEmpty then Lean.toolchain else env.initToolchain

/--
The binary search path of the environment (i.e., `PATH`).
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

/-- Environment variable settings that are not augmented by a Lake workspace. -/
def baseVars (env : Env) : Array (String × Option String)  :=
  #[
    ("ELAN_HOME", env.elan?.map (·.home.toString)),
    ("ELAN_TOOLCHAIN", if env.toolchain.isEmpty then none else env.toolchain),
    ("LAKE", env.lake.lake.toString),
    ("LAKE_HOME", env.lake.home.toString),
    ("LAKE_PKG_URL_MAP", toJson env.pkgUrlMap |>.compress),
    ("LEAN_SYSROOT", env.lean.sysroot.toString),
    ("LEAN_AR", env.lean.ar.toString),
    ("LEAN_CC", env.lean.leanCc?)
  ]

/-- Environment variable settings for the `Lake.Env`. -/
def vars (env : Env) : Array (String × Option String)  :=
  let vars := env.baseVars ++ #[
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
