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
public import Lake.Util.Version
public import Lean.Data.Json.FromToJson
import Lean.Environment
import Lean.Replay
import Init.Data.String.Search
import Init.Data.String.TakeDrop
import Init.Data.ToString.Macro
import Init.System.IO
import Init.System.Platform
import Std.Internal.UV.System

/-!
# Judging Lean code against the kernel, and against a challenge

Builds and exports Lean code, then establishes that it is accepted by the kernel and, where there
is a challenge to compare against, that it proves the challenge's statements using no axiom outside
a whitelist. This backs `lake comparator` and `lake check`.

The code being judged is adversarial input: it is built and exported inside a `bwrap` sandbox,
and no `.olean` produced from it is ever mapped into the process that reports the verdict. Only the
resulting NDJSON export crosses the boundary.
-/

namespace Lake.Check

inductive SandboxLocation where
  | noSandbox
  | path (path : String)

inductive ModuleKind where
  | check
  | solution
  | challenge
  deriving DecidableEq, Repr, Hashable

/--
The judgement for an individual step of the pipeline.
-/
public inductive StepJudgement where
  /--
  The step succeeded.
  -/
  | success
  /--
  Some error happened during the step.
  -/
  | failure
  /--
  The step was skipped, either because a previous step failed, or because it was unnecessary.
  -/
  | skipped
  deriving Lean.ToJson, Lean.FromJson, DecidableEq, Repr

/--
The final judgement for a whole problem.
-/
public inductive Judgement where
  /--
  The problem passed the check.
  -/
  | accepted
  /--
  The problem failed the check.
  -/
  | failure
  deriving Lean.ToJson, Lean.FromJson, DecidableEq, Repr

/--
Output of an individual checking step.
-/
public inductive Output where
  /--
  Some generic string output.
  -/
  | str (string : String)
  /-- Process output, note that the export itself from lean4export is left out for this. -/
  | proc (stdout : String) (stderr : String)
  deriving Lean.ToJson, Lean.FromJson, DecidableEq, Repr

def Output.append : Output → Output → Output
  | .str a, .str b => .str (a ++ b)
  | .proc o e, .proc o' e' => .proc (o ++ o') (e ++ e')
  | .str a, .proc o e => .proc (a ++ o) e
  | .proc o e, .str b => .proc (o ++ b) e

instance : Append Output := ⟨Output.append⟩

/--
The report on an individual checking step.
-/
public structure StepReport where
  /--
  The judgement of the step itself.
  -/
  judgement : StepJudgement
  /--
  Output recorded from the step if any.
  -/
  output : Output
  deriving Lean.ToJson, Lean.FromJson, DecidableEq, Repr

/--
A step of the checking pipelines.
-/
inductive Step where
  /--
  `lake resolve-deps`
  -/
  | resolveDependencies
  /-- `lake build` on the challenge/solution or the module that we check. -/
  | buildModule (kind : ModuleKind)
  /-- `lean4export` on the challenge/solution or the module that we check. -/
  | exportModule (kind : ModuleKind)
  /--
  Comparing statements in comparator.
  -/
  | compareStatements
  /--
  Checking absence of illegal axioms in comparator.
  -/
  | checkAxioms
  /--
  Checking the problem with the kernel named `name`.
  -/
  | kernel (name : String)
  deriving BEq, Hashable

structure State where
  /-- Steps recorded so far -/
  steps : Std.HashMap Step StepReport := {}
  /-- What the step running now reports as its output, if not the error it throws. -/
  output? : Option Output := none

/-- The report of `step`, which was skipped if it never ran. -/
def State.get (s : State) (step : Step) : StepReport :=
  s.steps.getD step { judgement := .skipped, output := .str "" }

structure Context where
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
  whichSandbox : SandboxLocation
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
  /-- The checkers `--paranoid` adds, each as a name and a command as for `externalKernels`. -/
  bundledKernels : Array (String × Array String)
  moduleStore : Std.HashMap ModuleKind System.FilePath
  /--
  Whether the run prints a JSON report instead of its progress.
  -/
  json : Bool

abbrev M := ReaderT Context <| StateRefT State IO

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

def progress (msg : String) : M Unit := do
  unless (← read).json do
    IO.println msg

/-- Adds `output` to what the step running now has output so far. -/
def appendOutput (output : Output) : M Unit :=
  modify fun s => { s with output? := some <| s.output?.elim output (· ++ output) }

/-- Passes on the standard error of a child whose standard out the run consumes itself. -/
def passStderr (stderr : String) : M Unit := do
  if (← read).json then
    appendOutput (.proc "" stderr)
  else
    IO.eprint stderr

def record (step : Step) (judgement : StepJudgement) (msg := "") : M Unit :=
  modify fun s => {
    steps := s.steps.insert step { judgement, output := s.output?.getD (.str msg) }
    output? := none
  }

/--
Runs `x` as `step`, which fails if `x` throws. Steps do not nest: what `x` outputs goes to the first
step that records, so `x` must not run later steps.
-/
def step (s : Step) (x : M α) : M α := do
  try
    let a ← x
    record s .success
    return a
  catch e =>
    record s .failure e.toString
    throw e

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
  that disable them ship it."

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
  match (← read).whichSandbox with
  | .noSandbox =>
    return {
      cmd := spawnArgs.cmd,
      args := spawnArgs.args,
      cwd := if let some cwd := spawnArgs.cwd then cwd else ← getProjectDir
      env := spawnArgs.envOverride
    }
  | .path whichSandbox =>
    return {
      cmd := (← read).whichEnvBin.toString
      args :=
        #["-i", whichSandbox]
          ++ buildSandboxArgs spawnArgs (← sandboxEnv spawnArgs) (← getProjectDir)
      cwd := ← getProjectDir
    }

open IO.Process in
partial def runSandBoxedWithStdoutTo (handle : IO.FS.Handle) (spawnArgs : SandboxArgs) : M Unit := do
  let (stderr, exitCode) ← pipedOutput (← sandboxSpawnArgs spawnArgs)
  passStderr stderr
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
  passStderr stderr
  if exitCode != 0 then
    throw <| .userError s!"Child exited with {exitCode}"
  return stdout

/--
Runs `spawnArgs` sandboxed, recording the output either to stdout or into JSON, returning the exit
code.
-/
def runSandBoxedExitCode (spawnArgs : SandboxArgs) : M UInt32 := do
  let args ← sandboxSpawnArgs spawnArgs
  if (← read).json then
    let { stdout, stderr, exitCode } ← IO.Process.output args
    appendOutput (.proc stdout stderr)
    return exitCode
  else
    let proc ← IO.Process.spawn args
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
def safeResolveWorkspace : M (String × String) := step .resolveDependencies do
  progress "Resolving dependencies"
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
def safeResolveDeps : M Unit := step .resolveDependencies do
  progress "Resolving dependencies"
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
def withSafeCheckExport (f : System.FilePath → M α) : M α := do
  if let some checkPath := (← read).moduleStore[ModuleKind.check]? then
    f checkPath
  else
    progress "Building and exporting"
    let projectDir ← getProjectDir
    IO.FS.withTempFile fun handle path => do
      step (.buildModule .check) <| runSandBoxedWithStdoutTo handle {
        cmd := (← read).whichLake.toString,
        args := #["check"],
        envPass := #["PATH", "HOME", "LEAN_ABORT_ON_PANIC"]
        envOverride := #[("LEAN_ABORT_ON_PANIC", some "1"), ("LAKE_CHECK_EXPORT", some "1")]
        readablePaths := #[projectDir, ← getLeanPrefix, ← getLakeHome]
        writablePaths := #[projectDir / ".lake"]
        tmpfsPaths := forbiddenPaths
      }
      f path

def safeLakeBuild (kind : ModuleKind) (targets : Array Lean.Name) :
    M Unit := step (.buildModule kind) do
  let targetArgs := targets.map (·.toString)
  let targetList := " ".intercalate targetArgs.toList
  progress s!"Building {targetList}"
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
def withRunExporter (kind : ModuleKind) (args : Array String) (f : System.FilePath → M α) :
    M α := do
  let projectDir ← getProjectDir
  let whichLean4Export := (← read).whichLean4Export
  IO.FS.withTempFile fun exportHandle exportPath => do
    step (.exportModule kind) <| runSandBoxedWithStdoutTo exportHandle {
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

def withSafeExport (kind : ModuleKind) (module : Lean.Name) (decls : Array Lean.Name)
    (f : System.FilePath → M α) : M α := do
  progress s!"Exporting {decls} from {module}"
  withRunExporter kind (#[module.toString, "--"] ++ decls.map (·.toString)) f

def withSafeBuildAndExport (kind : ModuleKind) (module : Lean.Name) (decls : Array Lean.Name) (f : System.FilePath → M α) :
    M α := do
  if let some modulePath := (← read).moduleStore[kind]? then
    f modulePath
  else
    safeLakeBuild kind #[module]
    withSafeExport kind module decls f

def runExternalKernel (kernelName : String) (kernelCommand : Array String)
    (solutionPath : System.FilePath) : M (Option String) := do
  progress s!"Running {kernelName} kernel on solution"
  -- just always put out a nanoda-like config file for now
  IO.FS.withTempFile fun configHandle configPath => do
    let legalAxioms ← getLegalAxioms
    configHandle.putStr <| Lean.Json.compress <| Lean.Json.mkObj [
      ("use_stdin", false),
      ("export_file_path", solutionPath.toString),
      ("permitted_axioms", .arr <| legalAxioms.map (.str ∘ Lean.Name.toString)),
      ("unpermitted_axiom_hard_error", false),
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
      cwd := some (← Std.Internal.UV.System.osTmpdir)
    }
    try
      let ret ← runSandBoxedExitCode spawnArgs
      if ret != 0 then
        progress s!"{kernelName} kernel rejected the solution"
        let msg := s!"{kernelName} exited with {ret}"
        record (.kernel kernelName) .failure msg
        return some msg
      else
        progress s!"{kernelName} kernel accepts the solution"
        record (.kernel kernelName) .success
        return none
    catch e => do
      progress s!"Error while interacting with {kernelName} kernel"
      let msg := s!"Error while interacting with {kernelName} kernel: {e.toString}"
      record (.kernel kernelName) .failure msg
      return some msg
where
  isNanodaKernel (kernelName : String) : Bool :=
    -- TODO: get rid of this heuristic
    kernelName.contains "noda"

def builtinKernelName : String := "Lean default"

def runBuiltinKernel (solutionPath : System.FilePath) : M (Option String) := do
  let cmd := #[(← read).whichLeanChecker.toString, "--silent", "--from-export"]
  runExternalKernel builtinKernelName cmd solutionPath

/-- Runs every checker the context names over the export, Lean's own kernel last. -/
def runKernels (exportPath : System.FilePath) : M Unit := do
  let mut result := none
  for (kernelName, kernelCommand) in ← getExternalKernels do
    result := result <|> (← runExternalKernel kernelName kernelCommand exportPath)
  for (kernelName, kernelCommand) in (← read).bundledKernels do
    result := result <|> (← runExternalKernel kernelName kernelCommand exportPath)
  result := result <|> (← runBuiltinKernel exportPath)
  if let some error := result then
    throw <| IO.userError error

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
  runKernels solutionExportPath
where
  verifyCompare : M Unit := do
    let theoremNames ← getTheoremNames
    let definitionNames ← getDefinitionNames
    let solution ← step .compareStatements do
      let challenge ← LeanExport.parseStream <| .ofHandle (← IO.FS.Handle.mk challengeExportPath .read)
      let solution ← LeanExport.parseStream <| .ofHandle (← IO.FS.Handle.mk solutionExportPath .read)
      let targets := (← getTheoremNames) ++ (← getLegalAxioms)
      IO.ofExcept <| compareAt challenge solution targets definitionNames (← primitiveTargets)
      return solution
    step .checkAxioms do
      IO.ofExcept <| checkAxioms solution theoremNames definitionNames (← getLegalAxioms)

def compareIt : M Unit := do
  let exportTargets := (← builtinTargets) ++ (← getTheoremNames) ++ (← getLegalAxioms)
    ++ (← primitiveTargets) ++ (← getDefinitionNames)

  let challengeModule ← getChallengeModule
  withSafeBuildAndExport .challenge challengeModule exportTargets fun challengeExportPath => do
    let solutionModule ← getSolutionModule
    withSafeBuildAndExport .solution solutionModule exportTargets fun solutionExportPath => do
      verifyMatch challengeExportPath solutionExportPath
      progress "Your solution is okay!"

public structure Config where
  challenge_module : String
  solution_module : String
  theorem_names : Array String
  definition_names : Option (Array String) := none
  permitted_axioms : Array String
  enable_nanoda? : Option Bool
  external_kernels? : Option (Std.TreeMap String (Array String))
  deriving Lean.FromJson, Lean.ToJson, Repr

/--
Report on a run of `lake comparator`.
-/
public structure CompareReport where
  /--
  `lake resolve-deps`.
  -/
  resolve_dependencies : StepReport
  /--
  `lake build Challenge`.
  -/
  build_challenge : StepReport
  /--
  `lean4export Challenge`.
  -/
  export_challenge : StepReport
  /--
  `lake build Solution`.
  -/
  build_solution : StepReport
  /--
  `lean4export Solution`.
  -/
  export_solution : StepReport
  /--
  Check that the statements from Challenge match the ones in Solution.
  -/
  compare_statements : StepReport
  /--
  Check that the statements from solution do not use illegal axioms.
  -/
  check_axioms : StepReport
  /--
  For each configured kernel its judgement.
  -/
  kernel_reports : Std.TreeMap String StepReport
  /--
  The comparator config repeated for ease of use.
  -/
  config : Config
  deriving Lean.FromJson, Lean.ToJson

/--
Report of a run of `lake check`.
-/
public structure CheckReport where
  /--
  `lake resolve-deps`.
  -/
  resolve_dependencies : StepReport
  /--
  `lake build`
  -/
  build_report : StepReport
  /--
  Check that the statements do not use non-standard axioms.
  -/
  check_axioms : StepReport
  /--
  For each configured kernel its judgement on the theorems.
  -/
  kernel_reports : Std.TreeMap String StepReport
  deriving Lean.FromJson, Lean.ToJson

/-- The version of the layout of `Report`. -/
public def Report.currentVersion : StdVer := { major := 0, minor := 1, patch := 0 }

/-- What `lake comparator --json` and `lake check --json` print. -/
public structure Report (α : Type) where
  /--
  Version of the reporting format.
  -/
  version : StdVer := Report.currentVersion
  /--
  Overall problem judgement.
  -/
  judgement : Judgement
  /--
  The command specific report.
  -/
  report : α
  /--
  Whether the run was done with a sandbox.
  -/
  sandboxed : Bool
  deriving Lean.FromJson, Lean.ToJson

public abbrev LakeComparatorReport := Report CompareReport
public abbrev LakeCheckReport := Report CheckReport

/-- Every kernel the run is to check with, including those it skipped. -/
def State.kernelReports (s : State) (ctx : Context) : Std.TreeMap String StepReport :=
  let names := ctx.externalKernels.keys.toArray ++ ctx.bundledKernels.map (·.1)
    |>.push builtinKernelName
  names.foldl (init := {}) fun reports name => reports.insert name (s.get (.kernel name))

def State.toCompareReport (s : State) (ctx : Context) (config : Config) : CompareReport where
  resolve_dependencies := s.get .resolveDependencies
  build_challenge := s.get <| .buildModule .challenge
  export_challenge := s.get <| .exportModule .challenge
  build_solution := s.get <| .buildModule .solution
  export_solution := s.get <| .exportModule .solution
  compare_statements := s.get .compareStatements
  check_axioms := s.get .checkAxioms
  kernel_reports := s.kernelReports ctx
  config

def State.toCheckReport (s : State) (ctx : Context) : CheckReport where
  resolve_dependencies := s.get .resolveDependencies
  build_report := s.get <| .buildModule .check
  check_axioms := s.get .checkAxioms
  kernel_reports := s.kernelReports ctx

/--
Runs `x` as the whole of a run, and reports the verdict: in JSON mode as the report `mkReport` makes
of the run's steps, otherwise by printing any error.
-/
def runReporting [Lean.ToJson α] (ctx : Context) (mkReport : State → α) (x : M Unit) :
    IO ExitCode := do
  let run : M Bool := do
    try
      x
      return true
    catch e =>
      unless ctx.json do
        IO.eprintln s!"error: {e}"
      return false
  let (accepted, state) ← run.run ctx |>.run {}
  if ctx.json then
    let report : Report α := {
      judgement := if accepted then .accepted else .failure
      report := mkReport state
      sandboxed := ctx.whichSandbox matches .path _
    }
    IO.println (Lean.toJson report).pretty
  return if accepted then 0 else 1

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
The checkers release toolchains bundle besides `leanchecker`, each as a name and a command as for
`Context.externalKernels`.
-/
def bundledKernels (lean : LeanInstall) : Array (String × Array String) :=
  let exe (name : String) := lean.binDir / name |>.addExtension System.FilePath.exeExtension
  #[
    ("Lean paranoid", #[(exe "leanchecker-paranoid").toString, "--silent", "--from-export"]),
    ("lean4lean", #[(exe "lean4lean").toString, "--import"]),
    ("nanoda", #[(exe "nanoda_bin").toString]),
    ("con-leche", #[(exe "con-leche").toString]),
    ("con-ron", #[(exe "con-ron").toString])
  ]

def resolveModuleStore (cmd : String)
    (entries : Array (String × ModuleKind × Option System.FilePath)) :
    IO (Except ExitCode (Std.HashMap ModuleKind System.FilePath)) := do
  let mut store := {}
  for (flag, kind, path?) in entries do
    let some path := path? | continue
    unless ← path.pathExists do
      return .error (← cannotRun s!"`lake {cmd} {flag}`: '{path}' does not exist")
    if ← path.isDir then
      return .error (← cannotRun s!"`lake {cmd} {flag}`: '{path}' is a directory")
    store := store.insert kind (← IO.FS.realPath path)
  return .ok store

/--
Resolves the external tools the commands need and builds the context they share, or reports why
that is not possible.
-/
def mkContext (cmd : String) (paranoid : Bool) (inadvisablyNoSandbox : Bool) (json : Bool)
    (lean : LeanInstall) (lake : LakeInstall) (projectDir : System.FilePath)
    (moduleStore : Std.HashMap ModuleKind System.FilePath) : IO (Except ExitCode Context) := do
  let whichSandbox ←
    if inadvisablyNoSandbox then
      -- The JSON report says so instead.
      unless json do
        IO.eprintln s!"WARNING: Sandbox disabled, this run is not trustworthy."
      pure .noSandbox
    else
      if !System.Platform.isLinux then
        return .error (← cannotRun
          s!"`lake {cmd}` sandboxes the code it checks with `bwrap`, which needs Linux namespaces.")

      let whichSandbox := (← IO.getEnv "COMPARATOR_BWRAP").getD "bwrap"
      let some sandboxPath ← whichExe whichSandbox
        | return .error (← cannotRun (missingSandboxError cmd whichSandbox))
      pure <| .path sandboxPath.toString
  -- Always the bundled exporter: the export format has to match the compiler that produced the
  -- oleans, so letting this be pointed elsewhere would reintroduce the toolchain-pinning problem.
  let whichLean4Export := lean.binDir / "leanexport" |>.addExtension System.FilePath.exeExtension
  let whichLeanChecker := lean.binDir / "leanchecker" |>.addExtension System.FilePath.exeExtension
  let some _ ← whichExe "git"
    | return .error (← cannotRun s!"`lake {cmd}` needs `git` on PATH to build inside the sandbox")
  let some envBinPath ← whichExe "env"
    | return .error (← cannotRun s!"`lake {cmd}` needs `env` on PATH to build inside the sandbox")
  let bundledKernels := if paranoid then Check.bundledKernels lean else #[]

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
    whichSandbox := whichSandbox
    whichLake := lake.lake
    lakeHome := lake.home
    whichLean4Export
    whichLeanChecker
    whichEnvBin := envBinPath
    externalKernels := {}
    bundledKernels
    moduleStore
    json
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
def checkUsedAxioms (exported : LeanExport.ExportedEnv) : M Unit := step .checkAxioms do
  let used := usedAxioms exported
  let msg :=
    if used.isEmpty then
      "Uses no axioms"
    else
      s!"Uses axioms: {", ".intercalate (used.toList.map (·.1.toString))}"
  progress msg
  let illegal := used.filter fun (ax, _) => !standardAxioms.contains ax
  unless illegal.isEmpty do
    throw <| .userError <| "\n".intercalate <| illegal.toList.map fun (ax, ref) =>
      s!"Axiom '{ax}' is not permitted; it is used by '{ref}'"
  appendOutput (.str msg)

/-- Checks a set of module roots at once against the kernel with no challenge to compare it to. -/
def checkProject : M Unit := do
  unless (← read).moduleStore.contains .check do
    safeResolveDeps
  withSafeCheckExport fun exportPath => do
    checkUsedAxioms (← LeanExport.parseStream <| .ofHandle (← IO.FS.Handle.mk exportPath .read))
    runKernels exportPath

/--
Runs `lake comparator`: builds and exports the challenge and the solution in a sandbox, then judges
the solution against the challenge.
-/
public def runComparator (configFile? : Option System.FilePath)
    (challengeFromExport? solutionFromExport? : Option System.FilePath) (paranoid : Bool)
    (inadvisablyNoSandbox : Bool) (json : Bool) (lean : LeanInstall) (lake : LakeInstall)
    (projectDir : System.FilePath) : IO ExitCode := do
  let resolved ← resolveModuleStore "comparator" #[
      ("--challenge-from-export", .challenge, challengeFromExport?),
      ("--solution-from-export", .solution, solutionFromExport?)
    ]
  let moduleStore ←
    match resolved with
    | .error rc => return rc
    | .ok store => pure store
  let base ←
    match ← mkContext "comparator" paranoid inadvisablyNoSandbox json lean lake projectDir
      moduleStore with
    | .error rc => return rc
    | .ok ctx => pure ctx

  let configFile := configFile?.getD "comparator.json"
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
  let ownKernels := base.bundledKernels.map (·.1) |>.push builtinKernelName
  if let some name := ownKernels.find? externalKernels.contains then
    return ← cannotRun s!"the external kernel `{name}` has the name of a kernel Lake runs itself"

  let needsProject := !(moduleStore.contains .challenge && moduleStore.contains .solution)
  if needsProject then
    if let some rc ← checkManifest "comparator" base.projectDir then
      return rc

  let ctx := { base with
    challengeModule := cfg.challenge_module.toName,
    solutionModule := cfg.solution_module.toName,
    theoremNames,
    definitionNames,
    legalAxioms := cfg.permitted_axioms.map String.toName,
    externalKernels
  }
  runReporting ctx (·.toCompareReport ctx cfg) do
    if needsProject then
      let (leanPath, binPath) ← safeResolveWorkspace
      withReader (fun ctx => { ctx with leanPath, binPath }) compareIt
    else
      compareIt

/--
Runs `lake check`: builds and exports the project's default targets in the sandbox and checks them
with the kernel, with no challenge to compare them against.
-/
public def runCheck (fromExport? : Option System.FilePath) (paranoid : Bool)
    (inadvisablyNoSandbox : Bool) (json : Bool) (lean : LeanInstall) (lake : LakeInstall)
    (projectDir : System.FilePath) : IO ExitCode := do
  let resolved ← resolveModuleStore "check" #[("--from-export", .check, fromExport?)]
  let moduleStore ←
    match resolved with
    | .error rc => return rc
    | .ok store => pure store
  let base ←
    match ← mkContext "check" paranoid inadvisablyNoSandbox json lean lake projectDir moduleStore with
    | .error rc => return rc
    | .ok ctx => pure ctx
  unless moduleStore.contains .check do
    if let some rc ← checkManifest "check" base.projectDir then
      return rc
  -- Checkers that police axioms themselves are held to the axioms `checkUsedAxioms` permits.
  let ctx := { base with legalAxioms := standardAxioms }
  runReporting ctx (·.toCheckReport ctx) checkProject

end Lake.Check
