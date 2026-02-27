module

prelude
public import Lake.Load.Config
public import Lake.Build.Context
public import Lake.CLI.Build
import Lake.Util.Git
import Lake.Build.Run
import Lake.Build.Targets
import Lake.Load.Workspace

open System (FilePath)

namespace Lake.Install

/-- Resolve the install bin directory (`~/.lake/bin`), creating it if needed. -/
public def installBinDir : IO FilePath := do
  let some home ← IO.getEnv "HOME"
    | throw <| IO.userError "HOME environment variable not set; `lake install` requires it"
  let binDir : FilePath := home / ".lake" / "bin"
  IO.FS.createDirAll binDir
  return binDir

/-- Build and install executables to the given bin directory. -/
public def installExes (ws : Workspace) (binDir : FilePath) (targetSpecs : List String)
    (buildConfig : BuildConfig) : LoggerIO PUnit := do
  let exes ←
    if targetSpecs.isEmpty then
      let exes := ws.root.leanExes
      if exes.isEmpty then
        error s!"package '{ws.root.baseName}' has no executable targets to install"
      pure exes
    else
      targetSpecs.toArray.mapM fun spec =>
        match parseExeTargetSpec ws spec with
        | .ok exe => pure exe
        | .error e => error e.toString
  for exe in exes do
    let exeFile ← ws.runBuild exe.fetch buildConfig
    let destFile := binDir / exe.fileName
    IO.FS.writeBinFile destFile (← IO.FS.readBinFile exeFile)
    IO.Prim.setAccessRights destFile 0o755  -- rwxr-xr-x
    logInfo s!"Installed {exe.name} to {destFile}"
  logInfo s!"Installed {exes.size} executable(s) to {binDir}"

/-- Clone a git repo to a temporary directory, build, and install its executables. -/
public def installFromGit (gitUrl : String) (branch? rev? : Option String)
    (config : LoadConfig) (binDir : FilePath) (targetSpecs : List String)
    (buildConfig : BuildConfig) : LoggerIO PUnit := do
  IO.FS.withTempDir fun tmpDir => do
    let repo := GitRepo.mk tmpDir
    logInfo s!"Cloning {gitUrl}..."
    repo.clone gitUrl
    if let some branch := branch? then
      logInfo s!"Checking out branch {branch}..."
      repo.checkoutBranch branch
    else if let some rev := rev? then
      logInfo s!"Checking out revision {rev}..."
      repo.checkoutDetach rev
    let config : LoadConfig :=
      {config with wsDir := tmpDir, pkgDir := tmpDir, configFile := tmpDir / config.relConfigFile}
    let ws ← loadWorkspace config
    installExes ws binDir targetSpecs buildConfig
