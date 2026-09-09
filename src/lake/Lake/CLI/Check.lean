/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lake.Check.Axioms
public import Lake.Check.Compare
public import Lake.Config.InstallPath
public import Lake.Util.Exit
public import Lean.Data.Json.FromToJson
import Lean.Environment
import Lean.Replay
import Init.Data.String.Search
import Init.Data.String.TakeDrop
import Init.Data.ToString.Macro
import Init.System.IO
import Init.System.Platform

/-!
# Judging Lean code against the kernel, and against a challenge

Builds and exports Lean code, then establishes that it is accepted by the kernel and, where there
is a challenge to compare against, that it proves the challenge's statements using no axiom outside
a whitelist. This backs `lake challenge` and `lake check`.

The code being judged is adversarial input: it is built and exported inside a `bwrap` sandbox,
and no `.olean` produced from it is ever mapped into the process that reports the verdict. Only the
resulting NDJSON export crosses the boundary.
-/

namespace Lake.Check

public structure Context where
  projectDir : System.FilePath
  challengeModule : Lean.Name
  solutionModule : Lean.Name
  theoremNames : Array Lean.Name
  definitionNames : Array Lean.Name
  legalAxioms : Array Lean.Name
  /-- Bound into the sandbox: an `elan` toolchain lives under the home directory it covers. -/
  leanPrefix : System.FilePath
  /-- The workspace's `LEAN_PATH`. Empty until `safeResolveWorkspace` records it. -/
  leanPath : String
  /--
  The workspace's `PATH`, so the exporter's own `lean` child resolves to this toolchain. Empty
  until `safeResolveWorkspace` records it.
  -/
  binPath : String
  whichSandbox : String
  whichLake : System.FilePath
  /--
  Bound into the sandbox. Redundant for a Lake co-located with the toolchain, but a Lake installed
  on its own keeps its `.olean`s outside `leanPrefix`, and cannot detect its own configuration
  without them.
  -/
  lakeHome : System.FilePath
  whichLean4Export : System.FilePath
  whichLeanChecker : System.FilePath
  whichEnvBin : System.FilePath
  externalKernels : (Std.TreeMap String (Array String))

public abbrev M := ReaderT Context IO

structure SandboxArgs where
  cmd : String
  args : Array String
  envPass : Array String
  envOverride : Array (String × Option String) := #[]
  /-- Bound back read-only over the covered home directories, so the run can still read these. -/
  readablePaths : Array System.FilePath
  writablePaths : Array System.FilePath
  /--
  Paths that get masked with a tmpfs so they exist but do not have the same content as the host
  system.
  -/
  tmpfsPaths : Array System.FilePath
  /-- Whether the child gets a network at all. `bwrap` cannot narrow one to particular ports. -/
  network : Bool := false
  /--
  Different working directory for the sandboxed process to operate in.
  -/
  cwd : Option System.FilePath := none

@[inline]
def getExternalKernels : M (Std.TreeMap String (Array String)) := do return (← read).externalKernels

@[inline]
def getTheoremNames : M (Array Lean.Name) := do return (← read).theoremNames

@[inline]
def getDefinitionNames : M (Array Lean.Name) := do return (← read).definitionNames

@[inline]
def getProjectDir : M System.FilePath := do return (← read).projectDir

@[inline]
def getLeanPrefix : M System.FilePath := do return (← read).leanPrefix

@[inline]
def getLakeHome : M System.FilePath := do return (← read).lakeHome

@[inline]
def getChallengeModule : M Lean.Name := do return (← read).challengeModule

@[inline]
def getSolutionModule : M Lean.Name := do return (← read).solutionModule

@[inline]
def getLegalAxioms : M (Array Lean.Name) := do return (← read).legalAxioms

/-- Resolves `exe` to an absolute path via `PATH`, or `none` if it is not there. -/
def whichExe (exe : String) : IO (Option System.FilePath) := do
  let out ←
    try IO.Process.output { cmd := "which", args := #[exe] }
    catch _ => return none
  if out.exitCode != 0 then
    return none
  let path := out.stdout.trimAscii.toString
  return if path.isEmpty then none else some (path : System.FilePath)

def missingSandboxError (cmd exe : String) : String :=
s!"`lake {cmd}` needs `{exe}` to sandbox the code it checks, and it was not found.

  Install `bubblewrap` from your distribution and put `bwrap` on PATH, or set
  COMPARATOR_BWRAP to its full path. It needs either unprivileged user
  namespaces or a `bwrap` installed setuid root, which is how distributions
  that disable them ship it.

  There is no unsandboxed mode: the code being checked is untrusted, and it
  is built and exported inside the sandbox."

/-- The environment the sandboxed child runs with; `envOverride` wins over `envPass`. -/
def sandboxEnv (spawnArgs : SandboxArgs) : IO (Array (String × String)) := do
  let mut env := #[]
  for name in spawnArgs.envPass do
    if let some value ← IO.getEnv name then
      env := env.push (name, value)
  for (name, value?) in spawnArgs.envOverride do
    env := env.filter (·.1 != name)
    if let some value := value? then
      env := env.push (name, value)
  return env

/--
Builds the `bwrap` command line.

`/` is bound read-only and the home directories are then covered with a `tmpfs`, so the code being
judged is built against the system it expects while none of the invoking user's files are readable.
Mounts apply in order, so `readablePaths` binds back what the run does need on top of those covers.
Only the paths in `writablePaths` are writable, and the network is a namespace rather than a filter:
a run either has one or has none at all.
-/
def buildSandboxArgs (spawnArgs : SandboxArgs) (env : Array (String × String))
    (projectDir : System.FilePath) : Array String :=
  let args := #[
    "--ro-bind", "/", "/",
    "--tmpfs", "/home",
    "--tmpfs", "/root",
    "--tmpfs", "/run/user",
    "--tmpfs", "/tmp",
    "--dir", "/tmp/home",
    "--dev", "/dev",
    "--proc", "/proc",
    "--clearenv"
  ]
  let args := spawnArgs.tmpfsPaths.foldl (init := args)
    (fun acc path => acc ++ #["--tmpfs", path.toString])
  let args := spawnArgs.readablePaths.foldl (init := args)
    (fun acc path => acc ++ #["--ro-bind", path.toString, path.toString])
  let args := spawnArgs.writablePaths.foldl (init := args)
    (fun acc path => acc ++ #["--bind", path.toString, path.toString])
  let args := env.foldl (init := args) (fun acc (name, value) => acc ++ #["--setenv", name, value])
  -- Set last, so it wins over an inherited one: the invoking user's `HOME` is no longer there to
  -- point at, and `git` and Lake's caches want somewhere writable. This one goes with the run.
  let args := args ++ #[
    "--setenv", "HOME", "/tmp/home",
    "--unshare-all",
    "--die-with-parent",
    "--new-session"
  ]
  let args := if spawnArgs.network then args ++ #["--share-net"] else args
  let args :=
    if let some cwd := spawnArgs.cwd then
      args ++ #["--chdir", cwd.toString]
    else
      args ++ #["--chdir", projectDir.toString]
  args ++ #["--", spawnArgs.cmd] ++ spawnArgs.args

/-- The `bwrap` invocation that puts `spawnArgs` under the sandbox. -/
def sandboxSpawnArgs (spawnArgs : SandboxArgs) : M IO.Process.SpawnArgs := do
  return {
    cmd := (← read).whichEnvBin.toString
    args :=
      #["-i", (← read).whichSandbox]
        ++ buildSandboxArgs spawnArgs (← sandboxEnv spawnArgs) (← getProjectDir)
    cwd := ← getProjectDir
  }

open IO.Process in
partial def runSandBoxedWithStdoutTo (handle : IO.FS.Handle) (spawnArgs : SandboxArgs) : M Unit := do
  let (stderr, exitCode) ← pipedOutput (← sandboxSpawnArgs spawnArgs)
  IO.eprint stderr
  if exitCode != 0 then
    throw <| .userError s!"Child exited with {exitCode}"
where
  pipedOutput (args : SpawnArgs) : IO (String × UInt32) := do
    let child ← spawn { args with stdout := .piped, stderr := .piped, stdin := .null }
    let stdout ← IO.asTask (prio := .dedicated) do
      let rec loop : IO Unit := do
        let buf ← child.stdout.read 4096
        if buf.isEmpty then
          handle.flush
          return ()
        else
          handle.write buf
          loop
      loop
    let stderr ← child.stderr.readToEnd
    let exitCode ← child.wait
    discard <| IO.ofExcept stdout.get
    return (stderr, exitCode)

def runSandBoxedWithStdout (spawnArgs : SandboxArgs) : M String := do
  let { stdout, stderr, exitCode } ← IO.Process.output (← sandboxSpawnArgs spawnArgs)
  IO.eprint stderr
  if exitCode != 0 then
    throw <| .userError s!"Child exited with {exitCode}"
  return stdout

/-- Runs `spawnArgs` sandboxed, letting its output through, and returns its exit code. -/
def runSandBoxedExitCode (spawnArgs : SandboxArgs) : M UInt32 := do
  let proc ← IO.Process.spawn (← sandboxSpawnArgs spawnArgs)
  proc.wait

def runSandBoxed (spawnArgs : SandboxArgs) : M Unit := do
  let ret ← runSandBoxedExitCode spawnArgs
  if ret != 0 then
    throw <| .userError s!"Child exited with {ret}"

/--
Materializes the project's dependencies into `.lake` and reports the environment the workspace
defines, as `(LEAN_PATH, PATH)`.

Resolution elaborates the project's configuration, which is code, so it must not run outside the
sandbox; this is also the only step permitted to reach the network. `lake env` resolves and reports
in one invocation, so the export step can run the exporter directly against the search path
recorded here.
-/
def safeResolveWorkspace : M (String × String) := do
  IO.println "Resolving dependencies"
  let projectDir ← getProjectDir
  let dotLakeDir := projectDir / ".lake"

  if !(← System.FilePath.pathExists dotLakeDir) then
    IO.FS.createDir dotLakeDir

  let whichLake := (← read).whichLake
  let out ← runSandBoxedWithStdout {
    cmd := whichLake.toString,
    args := #["env"],
    envPass := #["PATH", "LEAN_ABORT_ON_PANIC"]
    envOverride := #[("LEAN_ABORT_ON_PANIC", some "1")]
    readablePaths := #[projectDir, ← getLeanPrefix, ← getLakeHome]
    writablePaths := #[dotLakeDir]
    tmpfsPaths := #[]
    -- Fetching git dependencies is the one thing here that has to reach out.
    network := true
  }

  let mut leanPath := ""
  let mut binPath := ""
  for line in out.split '\n' |>.toStringList do
    if let some rest := line.dropPrefix? "LEAN_PATH=" then
      leanPath := rest.toString
    else if let some rest := line.dropPrefix? "PATH=" then
      binPath := rest.toString
  if leanPath.isEmpty || binPath.isEmpty then
    throw <| .userError "`lake env` did not report the project's search path"
  return (leanPath, binPath)

/--
Materializes the project's dependencies into `.lake`.

Resolution elaborates the project's configuration, which is code, so it runs in the sandbox; it is
also the only step permitted to reach the network. Nothing has to come back: the process that
exports loads the workspace itself and so already knows the search path.
-/
def safeResolveDeps : M Unit := do
  IO.println "Resolving dependencies"
  let projectDir ← getProjectDir
  let dotLakeDir := projectDir / ".lake"
  if !(← System.FilePath.pathExists dotLakeDir) then
    IO.FS.createDir dotLakeDir
  runSandBoxed {
    cmd := (← read).whichLake.toString,
    args := #["resolve-deps"],
    envPass := #["PATH", "HOME", "LEAN_ABORT_ON_PANIC"]
    envOverride := #[("LEAN_ABORT_ON_PANIC", some "1")]
    readablePaths := #[projectDir, ← getLeanPrefix, ← getLakeHome]
    writablePaths := #[dotLakeDir]
    tmpfsPaths := #[]
    -- Fetching git dependencies is the one thing here that has to reach out.
    network := true
  }

def forbiddenPaths : Array System.FilePath := #["/run", "/var"]

/--
Builds and exports the project in one sandboxed `lake` process, and returns the export.

`LAKE_CHECK_EXPORT` puts that process into the half of `lake check` that runs inside the sandbox,
so the modules to check never cross a process boundary: it resolves them, builds them and dumps the
export itself, writing the export to stdout and everything else to stderr.
-/
def withSafeBuildAndExport (f : System.FilePath → M α) : M α := do
  IO.println "Building and exporting"
  let projectDir ← getProjectDir
  IO.FS.withTempFile fun handle path => do
    runSandBoxedWithStdoutTo handle {
      cmd := (← read).whichLake.toString,
      args := #["check"],
      envPass := #["PATH", "HOME", "LEAN_ABORT_ON_PANIC"]
      envOverride := #[("LEAN_ABORT_ON_PANIC", some "1"), ("LAKE_CHECK_EXPORT", some "1")]
      readablePaths := #[projectDir, ← getLeanPrefix, ← getLakeHome]
      writablePaths := #[projectDir / ".lake"]
      tmpfsPaths := forbiddenPaths
    }
    f path

def safeLakeBuild (targets : Array Lean.Name) : M Unit := do
  let targetArgs := targets.map (·.toString)
  let targetList := " ".intercalate targetArgs.toList
  IO.println s!"Building {targetList}"
  let projectDir ← getProjectDir
  let dotLakeDir := projectDir / ".lake"

  if !(← System.FilePath.pathExists dotLakeDir) then
    IO.FS.createDir dotLakeDir

  let whichLake := (← read).whichLake
  runSandBoxed {
    cmd := whichLake.toString,
    args := #["build"] ++ targetArgs,
    envPass := #["PATH", "LEAN_ABORT_ON_PANIC"]
    envOverride := #[("LEAN_ABORT_ON_PANIC", some "1")]
    readablePaths := #[projectDir, ← getLeanPrefix, ← getLakeHome]
    writablePaths := #[dotLakeDir]
    tmpfsPaths := forbiddenPaths
  }

/-- Runs the bundled exporter in the sandbox, with the grants every export needs. -/
def withRunExporter (args : Array String) (f : System.FilePath → M α) : M α := do
  let projectDir ← getProjectDir
  let whichLean4Export := (← read).whichLean4Export
  IO.FS.withTempFile fun exportHandle exportPath => do
    runSandBoxedWithStdoutTo exportHandle {
      cmd := whichLean4Export.toString
      args
      envPass := #["PATH", "LEAN_PATH", "LEAN_ABORT_ON_PANIC"]
      envOverride := #[("LEAN_ABORT_ON_PANIC", some "1"), ("LEAN_PATH", some (← read).leanPath),
        ("PATH", some (← read).binPath)]
      readablePaths := #[projectDir, projectDir / ".lake", ← getLeanPrefix, whichLean4Export]
      writablePaths := #[]
      tmpfsPaths := forbiddenPaths
    }
    f exportPath

def withSafeExport (module : Lean.Name) (decls : Array Lean.Name) (f : System.FilePath → M α) :
    M α := do
  IO.println s!"Exporting {decls} from {module}"
  withRunExporter (#[module.toString, "--"] ++ decls.map (·.toString)) f

def runExternalKernel (kernelName : String) (kernelCommand : Array String)
    (solutionPath : System.FilePath) : M (Option String) := do
  IO.println s!"Running {kernelName} kernel on solution"
  -- just always put out a nanoda-like config file for now
  IO.FS.withTempFile fun configHandle configPath => do
    let legalAxioms ← getLegalAxioms
    configHandle.putStr <| Lean.Json.compress <| Lean.Json.mkObj [
      ("use_stdin", false),
      ("export_file_path", solutionPath.toString),
      ("permitted_axioms", .arr <| legalAxioms.map (.str ∘ Lean.Name.toString)),
      ("unpermitted_axiom_hard_error", true),
      ("num_threads", 4),
      ("nat_extension", true),
      ("string_extension", true),
    ]
    configHandle.flush

    let mut kernelArgs := kernelCommand[1...*].toArray
    if isNanodaKernel kernelName then
      kernelArgs := kernelArgs.push configPath.toString
    else
      kernelArgs := kernelArgs.push solutionPath.toString

    -- Resolved rather than left to `PATH`: an external kernel installed under the home directory
    -- the sandbox covers has to be bound back, which needs its path.
    let kernelExe := (← whichExe kernelCommand[0]!).getD kernelCommand[0]!
    let spawnArgs := {
      cmd := kernelExe.toString,
      args := kernelArgs,
      envPass := #["LEAN_ABORT_ON_PANIC"],
      envOverride := #[("LEAN_ABORT_ON_PANIC", some "1")]
      readablePaths := #[configPath.toString, solutionPath.toString, kernelExe, ← getLeanPrefix]
      writablePaths := #[]
      tmpfsPaths := forbiddenPaths
      cwd := some "/tmp"
    }
    try
      let ret ← runSandBoxedExitCode spawnArgs
      if ret != 0 then
        IO.println s!"{kernelName} kernel rejected the solution"
        return some s!"{kernelName} exited with {ret}"
      else
        IO.println s!"{kernelName} kernel accepts the solution"
        return none
    catch e => do
      IO.println s!"Error while interacting with {kernelName} kernel"
      return some s!"Error while interacting with {kernelName} kernel: {e.toString}"
where
  isNanodaKernel (kernelName : String) : Bool :=
    -- TODO: get rid of this heuristic
    kernelName.contains "noda"

def runBuiltinKernel (solutionPath : System.FilePath) : M (Option String) := do
  let cmd := #[(← read).whichLeanChecker.toString, "--silent", "--from-export"]
  runExternalKernel "Lean default" cmd solutionPath

def primitiveTargets : M (Array Lean.Name) := do
  -- The challenge needs to have all the built-in constants of the kernel, as the
  -- kernel makes no guarantees when fed other definitions here.
  -- List from `git grep new_persistent_expr_const src/kernel/`
  return #[
    -- ``Nat.zero,
    -- ``Nat.succ,
    ``Nat.add,
    ``Nat.sub,
    ``Nat.mul,
    ``Nat.pow,
    ``Nat.gcd,
    ``Nat.div,
    ``Nat.mod,
    ``Nat.beq,
    ``Nat.ble,
    ``Nat.land,
    ``Nat.lor,
    ``Nat.xor,
    ``Nat.shiftLeft,
    ``Nat.shiftRight,
    ``String.ofList,
    ``Char.ofNat,
    ``List,
    ``eagerReduce,
    ``Nat,
    ``String,
    ``String.mk,
    ``Char,
    ``optParam,
    ``autoParam,
    ``semiOutParam,
    ``outParam
  ]

def builtinTargets : M (Array Lean.Name) := do
  let mut additional := #[]
  if (← getLegalAxioms).contains ``Quot.sound then
    additional := additional ++ #[``Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind]
  return additional

def verifyMatch (challengeExportPath : System.FilePath) (solutionExportPath : System.FilePath) :
    M Unit := do
  verifyCompare
  verifyKernels
where
  verifyCompare : M Unit := do
    let challenge ← LeanExport.parseStream <| .ofHandle (← IO.FS.Handle.mk challengeExportPath .read)
    let solution ← LeanExport.parseStream <| .ofHandle (← IO.FS.Handle.mk solutionExportPath .read)
    let theoremNames ← getTheoremNames
    let definitionNames ← getDefinitionNames
    let targets := (← getTheoremNames) ++ (← getLegalAxioms)
    IO.ofExcept <| compareAt challenge solution targets definitionNames (← primitiveTargets)
    IO.ofExcept <| checkAxioms solution theoremNames definitionNames (← getLegalAxioms)

  verifyKernels : M Unit := do
    let mut result := none
    for (kernelName, kernelCommand) in ← getExternalKernels do
      result := result <|> (← runExternalKernel kernelName kernelCommand solutionExportPath)
    result := result <|> (← runBuiltinKernel solutionExportPath)
    if let some error := result then
      throw <| IO.userError error

public def compareIt : M Unit := do
  let exportTargets := (← builtinTargets) ++ (← getTheoremNames) ++ (← getLegalAxioms)
    ++ (← primitiveTargets) ++ (← getDefinitionNames)

  let challengeModule ← getChallengeModule
  safeLakeBuild #[challengeModule]
  withSafeExport challengeModule exportTargets fun challengeExportPath => do
    let solutionModule ← getSolutionModule
    safeLakeBuild #[solutionModule]
    withSafeExport solutionModule exportTargets fun solutionExportPath => do
      verifyMatch challengeExportPath solutionExportPath
      IO.println "Your solution is okay!"

public structure Config where
  challenge_module : String
  solution_module : String
  theorem_names : Array String
  definition_names : Option (Array String) := none
  permitted_axioms : Array String
  enable_nanoda? : Option Bool
  external_kernels? : Option (Std.TreeMap String (Array String))
  deriving Lean.FromJson, Lean.ToJson, Repr

/-- Reports a failure to even start, which is distinct from a judgment. -/
def cannotRun (msg : String) : IO ExitCode := do
  IO.eprintln s!"error: {msg}"
  return 2

/--
Reports whether the project carries the manifest that sandboxed dependency resolution needs.

Resolution writes the manifest, and the sandbox does not grant write access to the project
directory, so a project without one fails inside the sandbox with a bare `permission denied`.
-/
def checkManifest (cmd : String) (projectDir : System.FilePath) : IO (Option ExitCode) := do
  if ← (projectDir / "lake-manifest.json").pathExists then
    return none
  return some (← cannotRun s!"'{projectDir}' has no `lake-manifest.json`, and `lake {cmd}` resolves \
    dependencies inside a sandbox that cannot write to the project directory. Run `lake build` \
    there first.")

/--
Resolves the external tools the commands need and builds the context they share, or reports why
that is not possible.
-/
def mkContext (cmd : String) (lean : LeanInstall) (lake : LakeInstall)
    (projectDir : System.FilePath) : IO (Except ExitCode Context) := do
  if !System.Platform.isLinux then
    return .error (← cannotRun
      s!"`lake {cmd}` sandboxes the code it checks with `bwrap`, which needs Linux namespaces. \
      There is no unsandboxed mode, so the command is unavailable on this platform.")

  let whichSandbox := (← IO.getEnv "COMPARATOR_BWRAP").getD "bwrap"
  let some sandboxPath ← whichExe whichSandbox
    | return .error (← cannotRun (missingSandboxError cmd whichSandbox))
  -- Always the bundled exporter: the export format has to match the compiler that produced the
  -- oleans, so letting this be pointed elsewhere would reintroduce the toolchain-pinning problem.
  let whichLean4Export := lean.binDir / "leanexport" |>.addExtension System.FilePath.exeExtension
  let whichLeanChecker := lean.binDir / "leanchecker" |>.addExtension System.FilePath.exeExtension
  let some _ ← whichExe "git"
    | return .error (← cannotRun s!"`lake {cmd}` needs `git` on PATH to build inside the sandbox")
  let some envBinPath ← whichExe "env"
    | return .error (← cannotRun s!"`lake {cmd}` needs `env` on PATH to build inside the sandbox")

  return .ok {
    projectDir := ← IO.FS.realPath projectDir
    challengeModule := .anonymous
    solutionModule := .anonymous
    theoremNames := #[]
    definitionNames := #[]
    legalAxioms := #[]
    leanPrefix := lean.sysroot
    leanPath := ""
    binPath := ""
    whichSandbox := sandboxPath.toString
    whichLake := lake.lake
    lakeHome := lake.home
    whichLean4Export
    whichLeanChecker
    whichEnvBin := envBinPath
    externalKernels := {}
  }

/-- Resolves the external kernels a configuration asks for. -/
def resolveExternalKernels (cfg : Config) : IO (Except ExitCode (Std.TreeMap String (Array String))) := do
  let mut externalKernels := cfg.external_kernels?.getD {}
  if cfg.enable_nanoda?.getD false && !externalKernels.isEmpty then
    return .error (← cannotRun "cannot use `enable_nanoda` and `external_kernels` at the same \
      time; register nanoda in the list instead")
  for (kernelName, kernelCommand) in externalKernels do
    if kernelCommand.isEmpty then
      return .error (← cannotRun s!"`{kernelName}` has an empty command")
  if cfg.enable_nanoda?.getD false then
    externalKernels := externalKernels.insert "nanoda" #["nanoda_bin"]
  for (kernelName, kernelCommand) in externalKernels do
    if (← whichExe kernelCommand[0]!).isNone then
      return .error (← cannotRun s!"`{kernelName}` kernel `{kernelCommand[0]!}` was not found")
  return .ok externalKernels

def standardAxioms : Array Lean.Name :=
  #[``propext, ``Classical.choice, ``Quot.sound]

/-- Reports the axioms the checked modules rest on, and rejects any beyond `standardAxioms`. -/
def checkUsedAxioms (exported : LeanExport.ExportedEnv) : M Unit := do
  let used := usedAxioms exported
  if used.isEmpty then
    IO.println "Uses no axioms"
  else
    IO.println s!"Uses axioms: {", ".intercalate (used.toList.map (·.1.toString))}"
  let illegal := used.filter fun (ax, _) => !standardAxioms.contains ax
  unless illegal.isEmpty do
    throw <| .userError <| "\n".intercalate <| illegal.toList.map fun (ax, ref) =>
      s!"Axiom '{ax}' is not permitted; it is used by '{ref}'"

/-- Checks a set of module roots at once against the kernel with no challenge to compare it to. -/
def checkProject : M Unit := do
  safeResolveDeps
  withSafeBuildAndExport fun exportPath => do
    if let some error ← runBuiltinKernel exportPath then
      throw <| .userError error
    let exported ← LeanExport.parseStream <| .ofHandle (← IO.FS.Handle.mk exportPath .read)
    checkUsedAxioms exported

/--
Runs `lake challenge`: builds and exports the challenge and the solution in a sandbox, then judges
the solution against the challenge.
-/
public def runChallenge (configFile? : Option System.FilePath) (lean : LeanInstall)
    (lake : LakeInstall) (projectDir : System.FilePath) : IO ExitCode := do
  let base ←
    match ← mkContext "challenge" lean lake projectDir with
    | .error rc => return rc
    | .ok ctx => pure ctx

  let some configFile := configFile?
    | return ← cannotRun "no challenge configuration given; pass `--config <file>`"
  let contents ←
    try IO.FS.readFile configFile
    catch e => return ← cannotRun s!"could not read the configuration: {e}"
  let cfg ←
    match Lean.Json.parse contents >>= Lean.fromJson? (α := Config) with
    | .error e => return ← cannotRun s!"malformed configuration in '{configFile}': {e}"
    | .ok cfg => pure cfg

  let theoremNames := cfg.theorem_names.map String.toName
  let definitionNames := cfg.definition_names.getD #[] |>.map String.toName
  if theoremNames.isEmpty && definitionNames.isEmpty then
    return ← cannotRun "nothing to check: the configuration names no theorems or definitions"
  let externalKernels ←
    match ← resolveExternalKernels cfg with
    | .error rc => return rc
    | .ok ks => pure ks

  if let some rc ← checkManifest "challenge" base.projectDir then
    return rc

  try
    let ctx := { base with
      challengeModule := cfg.challenge_module.toName,
      solutionModule := cfg.solution_module.toName,
      theoremNames,
      definitionNames,
      legalAxioms := cfg.permitted_axioms.map String.toName,
      externalKernels
    }
    let (leanPath, binPath) ← ReaderT.run safeResolveWorkspace ctx
    ReaderT.run compareIt { ctx with leanPath, binPath }
    return 0
  catch e =>
    IO.eprintln s!"error: {e}"
    return 1

/--
Runs `lake check`: builds and exports the project's default targets in the sandbox and checks them
with the kernel, with no challenge to compare them against.
-/
public def runCheck (lean : LeanInstall) (lake : LakeInstall)
    (projectDir : System.FilePath) : IO ExitCode := do
  let base ←
    match ← mkContext "check" lean lake projectDir with
    | .error rc => return rc
    | .ok ctx => pure ctx
  if let some rc ← checkManifest "check" base.projectDir then
    return rc
  try
    checkProject.run base
    return 0
  catch e =>
    IO.eprintln s!"error: {e}"
    return 1

end Lake.Check
