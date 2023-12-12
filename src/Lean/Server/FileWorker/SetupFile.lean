/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Marc Huisinga
-/
import Init.System.IO
import Lean.Server.Utils
import Lean.Util.FileSetupInfo
import Lean.Util.LakePath
import Lean.LoadDynlib

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
    args := args.push "--no-build"
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
  let stderr ← IO.asTask (processStderr "") Task.Priority.dedicated

  let stdout := String.trim (← lakeProc.stdout.readToEnd)
  let stderr ← IO.ofExcept stderr.get
  let exitCode ← lakeProc.wait
  return ⟨spawnArgs, exitCode, stdout, stderr⟩

inductive FileSetupResultKind where
  | success
  | noLakefile
  | importsOutOfDate
  | error (msg : String)

structure FileSetupResult where
  kind          : FileSetupResultKind
  srcSearchPath : SearchPath
  fileOptions   : Options

def FileSetupResult.ofSuccess (pkgSearchPath : SearchPath) (fileOptions : Options)
    : IO FileSetupResult := do return {
  kind          := FileSetupResultKind.success
  srcSearchPath := ← initSrcSearchPath pkgSearchPath,
  fileOptions
}

def FileSetupResult.ofNoLakefile : IO FileSetupResult := do return {
  kind          := FileSetupResultKind.noLakefile
  srcSearchPath := ← initSrcSearchPath
  fileOptions   := Options.empty
}

def FileSetupResult.ofImportsOutOfDate : IO FileSetupResult := do return {
  kind          := FileSetupResultKind.importsOutOfDate
  srcSearchPath := ← initSrcSearchPath
  fileOptions   := Options.empty
}

def FileSetupResult.ofError (msg : String) : IO FileSetupResult := do return {
  kind          := FileSetupResultKind.error msg
  srcSearchPath := ← initSrcSearchPath
  fileOptions   := Options.empty
}

def FileSetupResult.addGlobalOptions (result : FileSetupResult) (globalOptions : Options)
    : FileSetupResult :=
  let fileOptions := globalOptions.mergeBy (fun _ _ fileOpt => fileOpt) result.fileOptions
  { result with fileOptions := fileOptions }

/-- Uses `lake setup-file` to compile dependencies on the fly and add them to `LEAN_PATH`.
Compilation progress is reported to `handleStderr`. Returns the search path for
source files and the options for the file. -/
partial def setupFile (m : DocumentMeta) (imports : Array Import) (handleStderr : String → IO Unit) : IO FileSetupResult := do
  let some filePath := System.Uri.fileUriToPath? m.uri
    | return ← FileSetupResult.ofNoLakefile -- untitled files have no lakefile

  -- NOTE: we assume for now that `lakefile.lean` does not have any non-core-Lean deps
  -- NOTE: lake does not exist in stage 0 (yet?)
  if filePath.fileName == "lakefile.lean" then
    return ← FileSetupResult.ofNoLakefile -- the lakefile itself has no lakefile

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
    let pkgSearchPath ← info.paths.srcPath.mapM realPathNormalized
    FileSetupResult.ofSuccess pkgSearchPath info.setupOptions.toOptions
  | 2 => -- exit code for lake reporting that there is no lakefile
    FileSetupResult.ofNoLakefile
  | 3 => -- exit code for `--no-build`
    FileSetupResult.ofImportsOutOfDate
  | _ =>
    FileSetupResult.ofError s!"`{cmdStr}` failed:\n{result.stdout}\nstderr:\n{result.stderr}"
