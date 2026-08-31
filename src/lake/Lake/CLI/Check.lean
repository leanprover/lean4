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

The code being judged is adversarial input: it is built and exported inside a `landrun` sandbox,
and no `.olean` produced from it is ever mapped into this process. Only the resulting NDJSON export
crosses the boundary.
-/

namespace Lake.Check

public structure Context where
  projectDir : System.FilePath
  challengeModule : Lean.Name
  solutionModule : Lean.Name
  theoremNames : Array Lean.Name
  definitionNames : Array Lean.Name
  legalAxioms : Array Lean.Name
  /-- The workspace's `LEAN_PATH`. Empty until `safeResolveWorkspace` records it. -/
  leanPath : String
  /--
  The workspace's `PATH`, so the exporter's own `lean` child resolves to this toolchain. Empty
  until `safeResolveWorkspace` records it.
  -/
  binPath : String
  whichLandrun : String
  whichLake : System.FilePath
  whichLean4Export : System.FilePath
  externalKernels : (Std.TreeMap String (Array String))

public abbrev M := ReaderT Context IO

structure LandrunArgs where
  cmd : String
  args : Array String
  envPass : Array String
  envOverride : Array (String × Option String) := #[]
  readablePaths : Array System.FilePath
  writablePaths : Array System.FilePath
  /-- TCP ports the child may connect to. Landrun denies all of them by default. -/
  connectPorts : Array String := #[]

@[inline]
def getExternalKernels : M (Std.TreeMap String (Array String)) := do return (← read).externalKernels

@[inline]
def getTheoremNames : M (Array Lean.Name) := do return (← read).theoremNames

@[inline]
def getDefinitionNames : M (Array Lean.Name) := do return (← read).definitionNames

@[inline]
def getProjectDir : M System.FilePath := do return (← read).projectDir

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

def missingLandrunError (cmd exe : String) : String :=
s!"`lake {cmd}` needs `{exe}` to sandbox the code it checks, and it was not found.

  Install it from https://github.com/Zouuup/landrun (build from `main`)
  and put it on PATH, or set COMPARATOR_LANDRUN to its full path.

  There is no unsandboxed mode: the code being checked is untrusted, and it
  is built and exported inside the sandbox."

def buildLandrunArgs (spawnArgs : LandrunArgs) : Array String :=
  -- Landlock rules are additive, so `--rox /` is read plus execute everywhere, narrowed back only
  -- by what is granted write access below. Naming executables individually would not confine them:
  -- Landlock checks execute permission at `execve`, on the binary and the ELF interpreter, and the
  -- loader will run any dynamically linked binary passed to it as an argument, mapping it with read
  -- access alone. See `helpChallenge` for what the sandbox does and does not bound.
  let args := #["--best-effort", "--rox", "/", "--rw", "/dev"]
  let args := spawnArgs.envPass.foldl (init := args) (fun acc env => acc ++ #["--env", env])
  let args := spawnArgs.readablePaths.foldl (init := args) (fun acc path => acc ++ #["--ro", path.toString])
  let args := spawnArgs.writablePaths.foldl (init := args) (fun acc path => acc ++ #["--rwx", path.toString])
  let args := spawnArgs.connectPorts.foldl (init := args) (fun acc port => acc ++ #["--connect-tcp", port])
  args ++ #["--", spawnArgs.cmd] ++ spawnArgs.args

def runSandBoxedWithStdout (spawnArgs : LandrunArgs) : M String := do
  let args := buildLandrunArgs spawnArgs
  let { stdout, stderr, exitCode } ← IO.Process.output {
    cmd := (← read).whichLandrun,
    args,
    env := spawnArgs.envOverride
    cwd := (← getProjectDir)
  }
  IO.eprint stderr
  if exitCode != 0 then
    throw <| .userError s!"Child exited with {exitCode}"
  return stdout


def runSandBoxed (spawnArgs : LandrunArgs) : M Unit := do
  let args := buildLandrunArgs spawnArgs
  let proc ← IO.Process.spawn {
    cmd := (← read).whichLandrun,
    args,
    env := spawnArgs.envOverride
    cwd := (← getProjectDir)
  }
  let ret ← proc.wait
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
    envPass := #["PATH", "HOME", "LEAN_ABORT_ON_PANIC"]
    envOverride := #[("LEAN_ABORT_ON_PANIC", some "1")]
    readablePaths := #[projectDir]
    writablePaths := #[dotLakeDir]
    -- `https` and `ssh`, the transports Lake's git dependencies use.
    connectPorts := #["443", "22"]
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

def safeLakeBuild (target : Lean.Name) : M Unit := do
  IO.println s!"Building {target}"
  let projectDir ← getProjectDir
  let dotLakeDir := projectDir / ".lake"

  if !(← System.FilePath.pathExists dotLakeDir) then
    IO.FS.createDir dotLakeDir

  let whichLake := (← read).whichLake
  runSandBoxed {
    cmd := whichLake.toString,
    args := #["build", target.toString],
    envPass := #["PATH", "HOME", "LEAN_ABORT_ON_PANIC"]
    envOverride := #[("LEAN_ABORT_ON_PANIC", some "1")]
    readablePaths := #[projectDir]
    writablePaths := #[dotLakeDir]
  }

def safeExport (module : Lean.Name) (decls : Array Lean.Name) : M String := do
  IO.println s!"Exporting {decls} from {module}"
  let baseArgs := #[module.toString, "--"]
  let args := decls.foldl (·.push <| ·.toString) baseArgs

  let projectDir ← getProjectDir
  let dotLakeDir := projectDir / ".lake"
  let whichLean4Export := (← read).whichLean4Export
  runSandBoxedWithStdout {
    cmd := whichLean4Export.toString
    args := args,
    envPass := #["PATH", "HOME", "LEAN_PATH", "LEAN_ABORT_ON_PANIC"]
    envOverride := #[("LEAN_ABORT_ON_PANIC", some "1"), ("LEAN_PATH", some (← read).leanPath),
      ("PATH", some (← read).binPath)]
    readablePaths := #[projectDir, dotLakeDir]
    writablePaths := #[]
  }

def runExternalKernel (kernelName : String) (kernelCommand : Array String)
    (solutionExport : String) : M (Option String) := do
  IO.println s!"Running {kernelName} kernel on solution"
  -- just always put out a nanoda-like config file for now
  IO.FS.withTempFile fun configHandle configPath => do
  IO.FS.withTempFile fun solutionHandle solutionPath => do
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

    solutionHandle.putStr solutionExport
    solutionHandle.flush

    let mut kernelArgs := kernelCommand[1...*].toArray
    if isNanodaKernel kernelName then
      kernelArgs := kernelArgs.push configPath.toString
    else
      kernelArgs := kernelArgs.push solutionPath.toString

    let spawnArgs := {
      cmd := kernelCommand[0]!,
      args := kernelArgs,
      envPass := #[]
      readablePaths := #[configPath.toString, solutionPath.toString]
      writablePaths := #[]
    }
    let args := buildLandrunArgs spawnArgs

    try
      let proc ← IO.Process.spawn {
        cmd := (← read).whichLandrun,
        args,
        env := spawnArgs.envOverride
        cwd := (← getProjectDir)
      }

      let ret ← proc.wait
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

def runBuiltinKernel (solution : LeanExport.ExportedEnv) : M (Option String) := do
  IO.println "Running Lean default kernel on solution."
  let env ← Lean.mkEmptyEnvironment
  let mut kernelEnv := env.toKernelEnv
  let origConstMap := solution.constMap
  -- Lean's kernel interprets just the addition of `Quot as adding all of these so adding them
  -- multiple times leads to errors.
  let quotTargets := [`Quot.mk, `Quot.lift, `Quot.ind]
  let kernelConstMap := quotTargets.foldl (init := origConstMap) (·.erase ·)
  try
    kernelEnv ← kernelEnv.replay kernelConstMap
    IO.println "Lean default kernel accepts the solution"
  catch e =>
    IO.println "Lean default kernel rejects the solution"
    return some e.toString

  try
    let verifyTargets := `Quot :: quotTargets
    for quotTarget in verifyTargets do
      if let some info := origConstMap[quotTarget]? then
        let some info' := kernelEnv.find? quotTarget |
          throw <| .userError s!"Could not find quotient constant in final kernel env: {quotTarget}"
        if info != info' then
          throw <| .userError s!"Quotient constant mismatch on: {quotTarget}"
    return none
  catch e =>
    IO.println "Quotient post-check rejects the solution"
    return some e.toString

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

def stringStream (s : String) : BaseIO IO.FS.Stream := do
  let ref ← IO.mkRef {
    data := s.toByteArray
  }
  return IO.FS.Stream.ofBuffer ref

def verifyMatch (challengeExport : String) (solutionExport : String) :
    M Unit := do
  let challenge ← LeanExport.parseStream (← stringStream challengeExport)
  let solution ← LeanExport.parseStream (← stringStream solutionExport)
  let theoremNames ← getTheoremNames
  let definitionNames ← getDefinitionNames
  let targets := (← getTheoremNames) ++ (← getLegalAxioms)
  IO.ofExcept <| compareAt challenge solution targets definitionNames (← primitiveTargets)
  IO.ofExcept <| checkAxioms solution theoremNames definitionNames (← getLegalAxioms)
  let mut result := none
  for (kernelName, kernelCommand) in ← getExternalKernels do
    result := result <|> (← runExternalKernel kernelName kernelCommand solutionExport)
  result := result <|> (← runBuiltinKernel solution)
  if let some error := result then
    throw <| IO.userError error

public def compareIt : M Unit := do
  let exportTargets := (← builtinTargets) ++ (← getTheoremNames) ++ (← getLegalAxioms)
    ++ (← primitiveTargets) ++ (← getDefinitionNames)

  let challengeModule ← getChallengeModule
  safeLakeBuild challengeModule
  let challengeExport ← safeExport challengeModule exportTargets

  let solutionModule ← getSolutionModule
  safeLakeBuild solutionModule
  let solutionExport ← safeExport solutionModule exportTargets

  verifyMatch challengeExport solutionExport

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
      s!"`lake {cmd}` sandboxes the code it checks with `landrun`, which needs Linux Landlock. \
      There is no unsandboxed mode, so the command is unavailable on this platform.")

  let whichLandrun := (← IO.getEnv "COMPARATOR_LANDRUN").getD "landrun"
  let some landrunPath ← whichExe whichLandrun
    | return .error (← cannotRun (missingLandrunError cmd whichLandrun))
  -- Always the bundled exporter: the export format has to match the compiler that produced the
  -- oleans, so letting this be pointed elsewhere would reintroduce the toolchain-pinning problem.
  let whichLean4Export := lean.binDir / "leanexport" |>.addExtension System.FilePath.exeExtension
  let some _ ← whichExe "git"
    | return .error (← cannotRun s!"`lake {cmd}` needs `git` on PATH to build inside the sandbox")

  return .ok {
    projectDir := ← IO.FS.realPath projectDir
    challengeModule := .anonymous
    solutionModule := .anonymous
    theoremNames := #[]
    definitionNames := #[]
    legalAxioms := #[]
    leanPath := ""
    binPath := ""
    whichLandrun := landrunPath.toString
    whichLake := lake.lake
    whichLean4Export
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

end Lake.Check
