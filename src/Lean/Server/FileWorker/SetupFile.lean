/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Marc Huisinga
-/
prelude
import Init.System.IO
import Lean.Server.Utils
import Lean.Util.FileSetupInfo
import Lean.Util.LakePath
import Lean.LoadDynlib
import Lean.Server.ServerTask

namespace Lean.Server.FileWorker

open IO

structure LakeSetupFileOutput where
    spawnArgs : Process.SpawnArgs
    exitCode  : UInt32
    stdout    : String
    stderr    : String

partial def runLakeSetupFile
    (m                 : DocumentMeta)
    (lakePath filePath : System.FilePath)
    (imports           : Array Import)
    (handleStderr      : String → IO Unit)
    : IO LakeSetupFileOutput := do
  let mut args := #["setup-file", filePath.toString] ++ imports.map (toString ·.module)
  if m.dependencyBuildMode matches .never then
    args := args.push "--no-build" |>.push "--no-cache"
  let spawnArgs : Process.SpawnArgs := {
    stdin  := Process.Stdio.null
    stdout := Process.Stdio.piped
    stderr := Process.Stdio.piped
    cmd    := lakePath.toString
    args
  }
  let lakeProc ← Process.spawn spawnArgs

  let rec processStderr (acc : String) : IO String := do
    let line ← lakeProc.stderr.getLine
    if line == "" then
      return acc
    else
      handleStderr line
      processStderr (acc ++ line)
  let stderr ← ServerTask.IO.asTask (processStderr "")

  let stdout := String.trim (← lakeProc.stdout.readToEnd)
  let stderr ← IO.ofExcept stderr.get
  let exitCode ← lakeProc.wait
  return ⟨spawnArgs, exitCode, stdout, stderr⟩

/-- Categorizes possible outcomes of running `lake setup-file`. -/
inductive FileSetupResultKind where
  /-- File configuration loaded and dependencies updated successfully. -/
  | success
  /-- No Lake project found, no setup was done. -/
  | noLakefile
  /-- Imports must be rebuilt but `--no-build` was specified. -/
  | importsOutOfDate
  /-- Other error during Lake invocation. -/
  | error (msg : String)

/-- Result of running `lake setup-file`. -/
structure FileSetupResult where
  /-- Kind of outcome. -/
  kind        : FileSetupResultKind
  /-- Additional options from successful setup, or else empty. -/
  fileOptions : Options
  /-- Lean plugins from successful setup, or else empty. -/
  plugins     : Array System.FilePath

def FileSetupResult.ofSuccess (fileOptions : Options)
    (plugins : Array System.FilePath) : IO FileSetupResult := do return {
  kind          := FileSetupResultKind.success
  fileOptions, plugins
}

def FileSetupResult.ofNoLakefile : IO FileSetupResult := do return {
  kind          := FileSetupResultKind.noLakefile
  fileOptions   := Options.empty
  plugins       := #[]
}

def FileSetupResult.ofImportsOutOfDate : IO FileSetupResult := do return {
  kind          := FileSetupResultKind.importsOutOfDate
  fileOptions   := Options.empty
  plugins       := #[]
}

def FileSetupResult.ofError (msg : String) : IO FileSetupResult := do return {
  kind          := FileSetupResultKind.error msg
  fileOptions   := Options.empty
  plugins       := #[]
}

/-- Uses `lake setup-file` to compile dependencies on the fly and add them to `LEAN_PATH`.
Compilation progress is reported to `handleStderr`. Returns the search path for
source files and the options for the file. -/
partial def setupFile (m : DocumentMeta) (imports : Array Import) (handleStderr : String → IO Unit) : IO FileSetupResult := do
  let some filePath := System.Uri.fileUriToPath? m.uri
    | return ← FileSetupResult.ofNoLakefile -- untitled files have no lakefile

  let lakePath ← determineLakePath
  if !(← System.FilePath.pathExists lakePath) then
    return ← FileSetupResult.ofNoLakefile

  let result ← runLakeSetupFile m lakePath filePath imports handleStderr

  let cmdStr := " ".intercalate (toString result.spawnArgs.cmd :: result.spawnArgs.args.toList)

  match result.exitCode with
  | 0 =>
    let Except.ok (info : FileSetupInfo) := Json.parse result.stdout >>= fromJson?
      | return ← FileSetupResult.ofError s!"Invalid output from `{cmdStr}`:\n{result.stdout}\nstderr:\n{result.stderr}"
    initSearchPath (← getBuildDir) info.paths.oleanPath
    info.paths.loadDynlibPaths.forM loadDynlib
    let pluginPaths ← info.paths.pluginPaths.mapM realPathNormalized
    FileSetupResult.ofSuccess info.setupOptions.toOptions pluginPaths
  | 2 => -- exit code for lake reporting that there is no lakefile
    FileSetupResult.ofNoLakefile
  | 3 => -- exit code for `--no-build`
    FileSetupResult.ofImportsOutOfDate
  | _ =>
    FileSetupResult.ofError s!"`{cmdStr}` failed:\n{result.stdout}\nstderr:\n{result.stderr}"
