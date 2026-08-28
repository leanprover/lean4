/-!
# Find deprecations

Reports deprecated modules, deprecated syntax usages, and deprecated options
whose `since` date is on or before a cutoff (i.e. old enough to be removed).

Usage: `lean --run script/find-deprecations.lean [--cutoff YYYY-MM-DD]`

`--cutoff` selects the latest `since` date to include; entries with a `since`
strictly greater than the cutoff are skipped. Defaults to 180 days ago.

Must be run from the `src/` directory and requires Lean to have been built
first, since the script loads the Lake workspace and imports built modules.
-/
import Lake.CLI.Main
import Lean

open Lean

def daysAgoISO (days : Nat) : IO String := do
  let gnu ← IO.Process.output {
    cmd := "date", args := #["-d", s!"{days} days ago", "+%Y-%m-%d"]
  }
  if gnu.exitCode == 0 then
    return gnu.stdout.trimAscii.toString
  let bsd ← IO.Process.output {
    cmd := "date", args := #["-v", s!"-{days}d", "+%Y-%m-%d"]
  }
  if bsd.exitCode == 0 then
    return bsd.stdout.trimAscii.toString
  throw <| .userError "could not compute default cutoff; pass --cutoff YYYY-MM-DD"

/-- Get the root package of the Lake workspace we are running in. -/
def getWorkspaceRoot : IO Lake.Package := do
  let (elanInstall?, leanInstall?, lakeInstall?) ← Lake.findInstall?
  let config ← Lake.MonadError.runEIO <| Lake.mkLoadConfig { elanInstall?, leanInstall?, lakeInstall? }
  let some workspace ← Lake.loadWorkspace config |>.toBaseIO
    | throw <| IO.userError "failed to load Lake workspace"
  return workspace.root

def getTargetModules : IO <| Array Name := do
  let workspaceRoot ← getWorkspaceRoot

  let res := workspaceRoot.defaultTargets.flatMap fun target =>
  if let some lib := workspaceRoot.findLeanLib? target then
      lib.roots
    else if let some exe := workspaceRoot.findLeanExe? target then
      #[exe.config.root]
    else
      #[]
  return res

def parseArgs (args : List String) : IO <| Option String := do
  match args with
  | [] => return none
  | "--cutoff" :: date :: [] => do
    pure date
  | _ => do throw <| .userError "unrecognized option"

def main (args : List String) : IO UInt32 := do
  let cutoff ← parseArgs args
  let cutoff := cutoff.getD (← daysAgoISO 180)

  let defaultTargets ← getTargetModules
  initSearchPath <| ← findSysroot

  let decls ← getOptionDeclsArray
  let mut deprecatedOptions : Array (Name × String):= #[]
  for (_, decl) in decls do
    let some dep := decl.deprecation? | continue
    unless dep.since > cutoff do
      deprecatedOptions := deprecatedOptions.push (decl.declName, dep.since)

  for currentModule in defaultTargets do
    IO.println s!"Checking module: {currentModule}"
    let currentModuleImport : Import := {module := currentModule}
    unsafe enableInitializersExecution
    let env ← importModules #[currentModuleImport] {} (trustLevel := 1024) (loadExts := true)
    let modNames := env.allImportedModuleNames
    for i in [0 : modNames.size] do
      let modName := modNames[i]!
      let some entry := env.getDeprecatedModuleByIdx? (i : ModuleIdx) | continue
      let some since := entry.since? | continue
      unless since > cutoff do
        let path ← findLean (← getSrcSearchPath) modName
        IO.println s!"deprecated module: {modName}, {since}, {path}"
      let deprecatedSyntax :=  Lean.Elab.deprecatedSyntaxExt.getModuleEntries env (i : ModuleIdx)
      for entry in deprecatedSyntax do
        let some since := entry.since? | continue
        unless since > cutoff do
          let some modIdx := env.getModuleIdxFor? entry.kind | continue
          let some modName := env.allImportedModuleNames[modIdx.toNat]? | continue
          let path ← findLean (← getSrcSearchPath) modName
          let some ranges := declRangeExt.find? (level := .server) env entry.kind
            | IO.eprintln s!"warning: no decl range for {entry.kind}; skipping"
              continue
          IO.println s!"deprecated syntax: {entry.kind}, {since}, {path}, {ranges.range.pos}, {ranges.range.endPos}"

    let mut remainingDeprecatedOptions : Array (Name × String) := #[]
    for (name, date) in deprecatedOptions do
      let some modIdx := env.getModuleIdxFor? name |
        remainingDeprecatedOptions := remainingDeprecatedOptions.push (name, date)
        continue
      let some modName := env.allImportedModuleNames[modIdx.toNat]? | continue
      let path ← findLean (← getSrcSearchPath) modName
      let some ranges := declRangeExt.find? (level := .server) env name
            | IO.eprintln s!"warning: no decl range for {name}; skipping"
              continue
      IO.println s!"deprecated option: {name}, {date}, {path}, {ranges.range.pos}, {ranges.range.endPos}"
    deprecatedOptions := remainingDeprecatedOptions

  return 0
