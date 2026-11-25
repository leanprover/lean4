/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
module

prelude
public import Lake.CLI.Check
public import Lake.Config.Env
import Init.Data.String.Search
import Init.Data.String.TakeDrop
import Init.Data.ToString.Macro
import Init.System.IO
import Init.System.Platform

/-!
# Running Lake commands in a sandbox

Loading a workspace elaborates its configuration files and building it runs its elaborators, so
every command that does either executes code from the project and its dependencies. On request,
such a command re-runs itself under the `bwrap` sandbox of `lake check`: the invoking user's files
are not readable, only `.lake` is writable, and only dependency resolution has a network.
-/

namespace Lake.Sandbox
open System (FilePath)

/-- What a sandboxed command may do beyond reading the project and writing its `.lake`. -/
public structure Policy where
  /-- The command is itself the dependency resolution, so it gets the network and the manifest. -/
  resolves : Bool := false
  /-- The command edits the project's sources. -/
  writesProject : Bool := false
  /-- The command still runs when dependency resolution fails. -/
  toleratesUnresolved : Bool := false

public structure Request where
  /-- The arguments `lake` was called with. -/
  args : Array String
  /-- The options among `args` that decide how the workspace is loaded. -/
  loadArgs : Array String
  wsDir : FilePath
  relManifestFile : FilePath
  lakeEnv : Lake.Env
  policy : Policy
  /-- Further variables for the command, on top of the inherited ones. -/
  env : Array (String × String) := #[]
  /-- Whether to return what the command writes to standard out instead of passing it on. -/
  captureStdout : Bool := false

/-- Variables the sandboxed command inherits. Anything else may hold a credential. -/
def inheritedVars : Array String := #[
  "PATH", "TERM", "COLORTERM", "NO_COLOR", "LANG", "LANGUAGE", "TZ", "USER", "LOGNAME", "SHELL",
  "LD_LIBRARY_PATH", "LIBRARY_PATH", "CPATH", "C_INCLUDE_PATH", "CC", "CXX",
  "SSL_CERT_FILE", "SSL_CERT_DIR", "CURL_CA_BUNDLE", "GIT_SSL_CAINFO",
  "http_proxy", "https_proxy", "no_proxy", "all_proxy",
  "HTTP_PROXY", "HTTPS_PROXY", "NO_PROXY", "ALL_PROXY",
  "RESERVOIR_API_URL", "RESERVOIR_API_BASE_URL"
]

/-- Prefixes of further variables the sandboxed command inherits. -/
def inheritedPrefixes : Array String := #["LEAN_", "LAKE_", "ELAN_", "LC_", "NIX_"]

/-- Variables withheld although `inheritedPrefixes` covers them. -/
def withheldVars : Array String := #["LAKE_CACHE_KEY"]

def isInherited (name : String) : Bool :=
  !withheldVars.contains name &&
    (inheritedVars.contains name || inheritedPrefixes.any (name.startsWith ·))

/-- This process's environment, which Linux exposes only through `/proc`. -/
def processEnv : IO (Array (String × String)) := do
  let bytes ← IO.FS.readBinFile "/proc/self/environ"
  let mut env := #[]
  let mut start := 0
  for i in [0:bytes.size] do
    if bytes[i]! == 0 then
      if let some entry := String.fromUTF8? (bytes.extract start i) then
        if let name :: value := entry.split '=' |>.toStringList then
          env := env.push (name, "=".intercalate value)
      start := i + 1
  return env

def isUnder (root path : FilePath) : Bool :=
  path == root || path.toString.startsWith (root.toString ++ "/")

/-- The home and temporary directories `Check.buildSandboxArgs` covers. -/
def coveredPaths : Array FilePath := #["/home", "/root", "/run/user", "/tmp"]

/--
The `PATH` inside the sandbox: `binDirs` first, so that `lean` and `lake` do not resolve to an
`elan` proxy under the covered home directory, and entries below `Check.forbiddenPaths` replaced by
what they link to, which keeps a system profile such as NixOS's `/run/current-system` usable.
-/
def sandboxPath (path : String) (binDirs : Array FilePath) : IO String := do
  let entries ← System.SearchPath.parse path |>.mapM fun entry => do
    if Check.forbiddenPaths.any (isUnder · entry) then
      try IO.FS.realPath entry catch _ => pure entry
    else
      pure entry
  return System.SearchPath.toString (binDirs.toList ++ entries).eraseDups

/-- The environment of the sandboxed command. -/
def sandboxEnv (lakeEnv : Lake.Env) : IO (Array (String × String)) := do
  let env := (← processEnv).filter (isInherited ·.1)
  let path := env.find? (·.1 == "PATH") |>.elim "" (·.2)
  let path ← sandboxPath path #[lakeEnv.lake.binDir, lakeEnv.lean.binDir]
  let env := env.filter (·.1 != "PATH") |>.push ("PATH", path)
  let env := env.push (Check.noSandboxEnvVar, "1")
  -- `HOME` moves into the sandbox, which must not move the system cache along with it.
  if let some cacheHome ← getSystemCacheHome? then
    return env.filter (·.1 != "XDG_CACHE_HOME") |>.push ("XDG_CACHE_HOME", cacheHome.toString)
  return env

/--
The Lake cache directories to keep writable. They are created only where the cache was asked for,
since a package can enable it too, and that is not known out here.
-/
def cacheDirs (lakeEnv : Lake.Env) : IO (Array FilePath) := do
  let mut dirs := #[]
  for cache? in [lakeEnv.lakeCache?, lakeEnv.lakeSystemCache?] do
    let some cache := cache? | continue
    if lakeEnv.enableArtifactCache? == some true then
      try IO.FS.createDirAll cache.dir catch _ => pure ()
    if ← cache.dir.pathExists then
      let dir ← IO.FS.realPath cache.dir
      unless dirs.contains dir do
        dirs := dirs.push dir
  return dirs

structure Tools where
  bwrap : FilePath
  env : FilePath

def unavailable (reason : String) : IO α :=
  throw <| .userError s!"{reason}\n\
    Use `--inadvisably-no-sandbox` or set `{Check.noSandboxEnvVar}=1` to run without the sandbox."

/-- Finds the `bwrap` to sandbox a command with, and checks that it can create namespaces. -/
def findTools : IO Tools := do
  unless System.Platform.isLinux do
    unavailable "the sandbox uses `bwrap`, which needs Linux namespaces"
  let exe := (← IO.getEnv "COMPARATOR_BWRAP").getD "bwrap"
  let some bwrap ← Check.whichExe exe
    | unavailable s!"the sandbox needs `{exe}` (bubblewrap), and it was not found"
  let some env ← Check.whichExe "env"
    | unavailable "the sandbox needs `env` on PATH"
  let probe ← IO.Process.output {
    cmd := env.toString
    args := #["-i", bwrap.toString, "--ro-bind", "/", "/", "--unshare-all", "--die-with-parent",
      "--", env.toString]
    stdin := .null
  }
  if probe.exitCode != 0 then
    unavailable s!"`{exe}` cannot create a sandbox here:\n{probe.stderr.trimAscii}"
  return { bwrap, env }

/-- Asks commands to sandbox themselves, like `--sandbox`. -/
def sandboxEnvVar : String := "LAKE_SANDBOX"

/--
Whether commands are to sandbox themselves: on request, by `requested` or the environment, and
unless the environment turns the sandbox off, which is also how a sandboxed command knows not to
sandbox itself again.
-/
public def isWanted (requested : Bool) : BaseIO Bool := do
  return (requested || (← IO.getEnv sandboxEnvVar) == some "1") &&
    (← IO.getEnv Check.noSandboxEnvVar) != some "1"

/--
Runs `x` with the manifest in place for the sandbox to bind, since `bwrap` cannot bind a file that
does not exist. An empty manifest counts as a missing one, and is removed again if `x` leaves it so.
-/
def withManifest (manifest : FilePath) (x : IO α) : IO α := do
  if ← manifest.pathExists then
    x
  else
    IO.FS.writeFile manifest ""
    try
      x
    finally
      if (← IO.FS.readFile manifest).isEmpty then
        IO.FS.removeFile manifest

/--
Re-runs the command of `req` under the sandbox and returns its exit code and, if asked for, its
standard out. Fails if there is no usable sandbox.

A command that is not the dependency resolution is preceded by one, a sandboxed `lake resolve-deps`,
because fetching dependencies needs a network and the command itself gets none.
-/
public def run (req : Request) : IO (ExitCode × String) := do
  let tools ← findTools
  let projectDir ← IO.FS.realPath req.wsDir
  let cwd ← IO.currentDir
  let lakeDir := projectDir / ".lake"
  let manifest := projectDir / req.relManifestFile
  let gitDir := projectDir / ".git"
  IO.FS.createDirAll lakeDir
  let env := (← sandboxEnv req.lakeEnv) ++ req.env
  let caches ← cacheDirs req.lakeEnv
  let protectedPaths := if ← gitDir.pathExists then #[gitDir] else #[]
  -- `bwrap` cannot change to a directory the covers hide, so it gets an empty one in its place.
  let cwdCover :=
    if !isUnder projectDir cwd && coveredPaths.any (isUnder · cwd) then #[cwd] else #[]
  let spawn (args : Array String) (resolves writesProject : Bool) (stdout : IO.Process.Stdio) :
      IO (ExitCode × String) := do
    let spec : Check.SandboxArgs := {
      cmd := req.lakeEnv.lake.lake.toString
      args
      envPass := #[]
      readablePaths :=
        #[projectDir, req.lakeEnv.lean.sysroot, req.lakeEnv.lake.home].toList.eraseDups.toArray
      writablePaths :=
        (if writesProject then #[projectDir] else #[lakeDir])
          ++ caches ++ (if resolves then #[manifest] else #[])
      protectedPaths := if writesProject then protectedPaths else #[]
      tmpfsPaths := (if resolves then #[] else Check.forbiddenPaths) ++ cwdCover
      network := resolves
      cwd := some cwd
    }
    let cmd := tools.env.toString
    let args := #["-i", tools.bwrap.toString] ++ Check.buildSandboxArgs spec env projectDir
    if req.captureStdout && stdout matches .inherit then
      let child ← IO.Process.spawn { cmd, args, stdout := .piped }
      let out ← child.stdout.readToEnd
      return (← child.wait, out)
    else
      let child ← IO.Process.spawn { cmd, args, stdout }
      return (← child.wait, "")
  let writesProject := req.policy.writesProject
  if req.policy.resolves then
    return ← withManifest manifest <| spawn req.args true writesProject .inherit
  -- Standard out belongs to the command itself.
  let (rc, _) ← withManifest manifest <| spawn (req.loadArgs ++ #["resolve-deps"]) true false .null
  if rc != 0 && !req.policy.toleratesUnresolved then
    return (rc, "")
  spawn req.args false writesProject .inherit
