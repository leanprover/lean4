/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lake.Config.Cache
public import Lake.Config.InstallPath

open System
open Lean hiding SearchPath

/-! # Lake's Environment
Definitions related to a Lake environment.
A Lake environment is computed on Lake's startup from
user-specified CLI options and the process environment.
-/

namespace Lake

/-- A Lake environment. -/
public structure Env where
  /-- The Lake installation of the environment. -/
  lake : LakeInstall
  /-- The Lean installation of the environment. -/
  lean : LeanInstall
  /-- The Elan installation (if any) of the environment. -/
  elan? : Option ElanInstall
  /-- The Reservoir API endpoint URL (e.g., `https://reservoir.lean-lang.org/api`). -/
  reservoirApiUrl : String
  /-- Overrides the detected Lean's githash as the string Lake uses for Lean traces. -/
  githashOverride : String
  /-- A name-to-URL mapping of URL overrides for the named packages. -/
  pkgUrlMap : NameMap String
  /--
  Whether to disable downloading build caches for packages. Set via `LAKE_NO_CACHE`.
  Can be overridden on a per-command basis with`--try-cache`.
  -/
  noCache : Bool
  /-- Whether the Lake artifact cache should be enabled by default (i.e., `LAKE_ARTIFACT_CACHE`). -/
  enableArtifactCache : Bool
  /--
  The system directory for the Lake cache. Set by `LAKE_CACHE_DIR`.
  If `none`, no suitable system directory for the cache exists.
  -/
  lakeCache? : Option Cache
  /-- The authentication key for cache uploads (i.e., `LAKE_CACHE_KEY`). -/
  cacheKey? : Option String
  /-- The base URL for artifact uploads and downloads from the cache (i.e., `LAKE_CACHE_ARTIFACT_ENDPOINT`). -/
  cacheArtifactEndpoint? : Option String
  /-- The base URL for revision uploads and downloads from the cache (i.e., `LAKE_CACHE_REVISION_ENDPOINT`). -/
  cacheRevisionEndpoint? : Option String
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
  /--
  The preferred toolchain of the environment. May be empty.

  Either `initToolchain` or, if none, Lake's `Lean.toolchain`.
  -/
  toolchain : String
  deriving Inhabited

/-- Returns the home directory of the current user (if possible). -/
public def getUserHome? : BaseIO (Option FilePath) := do
  if System.Platform.isWindows then
    let some drive ← IO.getEnv "HOMEDRIVE"
      | return none
    let some path ← IO.getEnv "HOMEPATH"
      | return none
    return drive ++ path
  else if let some home ← IO.getEnv "HOME" then
    return home
  else
    return none

/-- Returns the system directory that can be used to store caches (if one exists). -/
public def getSystemCacheHome? : BaseIO (Option FilePath) := do
  if let some cacheHome ← IO.getEnv "XDG_CACHE_HOME" then
    return FilePath.mk cacheHome
  else if let some userHome ← getUserHome? then
    return userHome / ".cache"
  else
    return none

namespace Env

/-- Compute the Lean toolchain string used by Lake from the process environment. -/
public def computeToolchain : BaseIO String := do
  return (← IO.getEnv "ELAN_TOOLCHAIN").getD Lean.toolchain

/--
Compute the system cache location from the process environment.
If `none`, no system directory for workspace the cache exists.
-/
public def computeCache? (elan? : Option ElanInstall) (toolchain : String) : BaseIO (Option Cache) := do
  if let some cacheDir ← IO.getEnv "LAKE_CACHE_DIR" then
    if cacheDir.isEmpty then
      return none
    else
      return some ⟨cacheDir⟩
  else if let some elan := elan? then
    return some ⟨elan.toolchainDir toolchain / "lake" / "cache"⟩
  else if let some cacheHome ← getSystemCacheHome? then
    return some ⟨cacheHome / "lake"⟩
  else
    return none

/--
Compute a `Lake.Env` object from the given installs
and the set environment variables.
-/
public def compute
  (lake : LakeInstall) (lean : LeanInstall) (elan? : Option ElanInstall)
  (noCache : Option Bool := none)
: EIO String Env := do
  let reservoirBaseUrl ← getUrlD "RESERVOIR_API_BASE_URL" "https://reservoir.lean-lang.org/api"
  let elanToolchain? ← IO.getEnv "ELAN_TOOLCHAIN"
  let initToolchain := elanToolchain?.getD ""
  let toolchain := elanToolchain?.getD Lean.toolchain
  return {
    lake, lean, elan?,
    pkgUrlMap := ← computePkgUrlMap
    reservoirApiUrl := ← getUrlD "RESERVOIR_API_URL" s!"{reservoirBaseUrl}/v1"
    noCache := (noCache <|> (← IO.getEnv "LAKE_NO_CACHE").bind envToBool?).getD false
    enableArtifactCache := (← IO.getEnv "LAKE_ARTIFACT_CACHE").bind envToBool? |>.getD false
    lakeCache? := ← computeCache? elan? toolchain
    cacheKey? := (← IO.getEnv "LAKE_CACHE_KEY").map (·.trim)
    cacheArtifactEndpoint? := (← IO.getEnv "LAKE_CACHE_ARTIFACT_ENDPOINT").map normalizeUrl
    cacheRevisionEndpoint? := (← IO.getEnv "LAKE_CACHE_REVISION_ENDPOINT").map normalizeUrl
    githashOverride := (← IO.getEnv "LEAN_GITHASH").getD ""
    toolchain
    initToolchain
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
  @[macro_inline] getUrlD var default := do
    if let some url ← IO.getEnv var then
      return normalizeUrl url
    else
       return default
  normalizeUrl url :=
    if url.back == '/' then url.dropRight 1 else url

/--
The string Lake uses to identify Lean in traces.
Either the environment-specified `LEAN_GITHASH` or the detected Lean's githash.

The override allows one to replace the Lean version used by a library
(e.g., Mathlib) without completely rebuilding it, which is useful for testing
custom builds of Lean.
-/
public def leanGithash (env : Env) : String :=
  if env.githashOverride.isEmpty then env.lean.githash else env.githashOverride

/--
The binary search path of the environment (i.e., `PATH`).
Combines the initial path of the environment with that of the Lake installation.
-/
public def path (env : Env) : SearchPath :=
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
public def leanPath (env : Env) : SearchPath :=
  env.lake.libDir :: env.initLeanPath

/--
The Lean source search path of the environment (i.e., `LEAN_SRC_PATH`).
Combines the initial path of the environment with that of the Lake and Lean
installations.
-/
public def leanSrcPath (env : Env) : SearchPath :=
  env.lake.srcDir :: env.initLeanSrcPath

/--
The shared library search path of the environment.
Combines the initial path of the environment with that of the Lean installation.
-/
public def sharedLibPath (env : Env) : SearchPath :=
  env.lean.sharedLibPath ++ env.initSharedLibPath

/-- Unset toolchain-specific environment variables. -/
public def noToolchainVars : Array (String × Option String) :=
  #[
    ("ELAN_TOOLCHAIN", none),
    ("LAKE", none),
    ("LAKE_OVERRIDE_LEAN", none),
    ("LAKE_HOME", none),
    ("LEAN", none),
    ("LEAN_GITHASH", none),
    ("LEAN_SYSROOT", none),
    ("LEAN_AR", none)
  ]

/-- Environment variable settings that are not augmented by a Lake workspace. -/
public def baseVars (env : Env) : Array (String × Option String)  :=
  #[
    ("ELAN", env.elan?.map (·.elan.toString)),
    ("ELAN_HOME", env.elan?.map (·.home.toString)),
    ("ELAN_TOOLCHAIN", if env.toolchain.isEmpty then none else env.toolchain),
    ("LAKE", env.lake.lake.toString),
    ("LAKE_HOME", env.lake.home.toString),
    ("LAKE_PKG_URL_MAP", toJson env.pkgUrlMap |>.compress),
    ("LAKE_NO_CACHE", toString env.noCache),
    ("LAKE_ARTIFACT_CACHE", toString env.enableArtifactCache),
    ("LAKE_CACHE_KEY", env.cacheKey?),
    ("LAKE_CACHE_ARTIFACT_ENDPOINT", env.cacheArtifactEndpoint?),
    ("LAKE_CACHE_REVISION_ENDPOINT", env.cacheRevisionEndpoint?),
    ("LEAN", env.lean.lean.toString),
    ("LEAN_SYSROOT", env.lean.sysroot.toString),
    ("LEAN_AR", env.lean.ar.toString),
    ("LEAN_CC", env.lean.leanCc?)
  ]

/-- Environment variable settings for the `Lake.Env`. -/
public def vars (env : Env) : Array (String × Option String)  :=
  let vars := env.baseVars ++ #[
    ("LAKE_CACHE_DIR", if let some cache := env.lakeCache? then cache.dir.toString else ""),
    ("LEAN_PATH", some env.leanPath.toString),
    ("LEAN_SRC_PATH", some env.leanSrcPath.toString),
    ("LEAN_GITHASH", env.leanGithash),
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
public def leanSearchPath (env : Lake.Env) : SearchPath :=
  env.lake.libDir :: env.lean.leanLibDir :: env.leanPath
