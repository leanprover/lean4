/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Marc Huisinga
-/
module

prelude
public import Lean.Server.Utils
public import Lean.Util.LakePath
public import Lean.Server.ServerTask

public section

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
    (header            : ModuleHeader)
    (handleStderr      : String → IO Unit)
    : IO LakeSetupFileOutput := do
  let mut args := #["setup-file", filePath.toString, "-"]
  if m.dependencyBuildMode matches .never then
    args := args.push "--no-build" |>.push "--no-cache"
  let spawnArgs : Process.SpawnArgs := {
    stdin  := Process.Stdio.piped
    stdout := Process.Stdio.piped
    stderr := Process.Stdio.piped
    cmd    := lakePath.toString
    args
  }
  let lakeProc ← Process.spawn spawnArgs
  let (stdin, lakeProc) ← lakeProc.takeStdin
  stdin.putStrLn (toJson header).compress

  let rec drainStderr (acc : String) : IO String := do
    let line ← lakeProc.stderr.getLine
    if line == "" then
      return acc
    else
      handleStderr line
      drainStderr (acc ++ line)
  let stderr ← ServerTask.IO.asTask (drainStderr "")

  let stdout := String.trimAscii (← lakeProc.stdout.readToEnd) |>.copy
  let stderr ← IO.ofExcept stderr.get
  let exitCode ← lakeProc.wait
  return ⟨spawnArgs, exitCode, stdout, stderr⟩

/-- Structured error output from `lake setup-file` failure. -/
structure LakeBuildError where
  summary : String
  buildDiagnostics : Array SerialMessage := #[]
  failedTargets : Array String := #[]
  deriving FromJson, ToJson

/-- Categorizes possible outcomes of running `lake setup-file`. -/
inductive FileSetupResultKind where
  /-- File configuration loaded and dependencies updated successfully. -/
  | success
  /-- No Lake project found, no setup was done. -/
  | noLakefile
  /-- Imports must be rebuilt but `--no-build` was specified. -/
  | importsOutOfDate
  /-- Other error during Lake invocation. -/
  | error (err : LakeBuildError)

/-- Result of running `lake setup-file`. -/
structure FileSetupResult where
  /-- Kind of outcome. -/
  kind        : FileSetupResultKind
  /-- Configuration from a successful setup, or else the default. -/
  setup       : ModuleSetup

def FileSetupResult.ofSuccess (setup : ModuleSetup) : IO FileSetupResult := do return {
  kind          := FileSetupResultKind.success
  setup
}

def FileSetupResult.ofNoLakefile (m : DocumentMeta) (header : ModuleHeader) : FileSetupResult := {
  kind          := FileSetupResultKind.noLakefile
  setup         := {name := m.mod, isModule := header.isModule}
}

def FileSetupResult.ofImportsOutOfDate (m : DocumentMeta) (header : ModuleHeader) : IO FileSetupResult := do return {
  kind          := FileSetupResultKind.importsOutOfDate
  setup         := {name := m.mod, isModule := header.isModule}
}

def FileSetupResult.ofError (m : DocumentMeta) (header : ModuleHeader) (err : LakeBuildError)
    : IO FileSetupResult := do return {
  kind          := FileSetupResultKind.error err
  setup         := {name := m.mod, isModule := header.isModule}
}

/-- Convert a 1-based Lean `Position` to a 0-based LSP `Position`. -/
private def leanPositionToLsp (p : Position) : Lsp.Position :=
  ⟨if p.line > 0 then p.line - 1 else 0, p.column⟩

private scoped instance : Coe MessageSeverity Lsp.DiagnosticSeverity where
  coe
    | .error => .error
    | .warning => .warning
    | .information => .information

/-- Convert a `SerialMessage` to an LSP diagnostic sourced from `"Lake"`. -/
private def serialMessageToDiagnostic (msg : SerialMessage) : Lsp.Diagnostic :=
  let startPos := leanPositionToLsp msg.pos
  let endPos := msg.endPos.map leanPositionToLsp |>.getD ⟨startPos.line, startPos.character + 1⟩
  let body := if msg.caption.trimAscii.isEmpty then msg.data.trimAscii.toString
    else s!"{msg.caption.trimAscii}:\n{msg.data.trimAscii}"
  { range := ⟨startPos, endPos⟩
    severity? := some msg.severity
    source? := some "Lake"
    message := body }

/-- Resolve a file name (possibly relative) to an absolute `DocumentUri`. -/
private def resolveFileUri (fileName : String) : IO Lsp.DocumentUri := do
  let path : System.FilePath := fileName
  let absPath ← if path.isAbsolute then pure path else pure ((← IO.currentDir) / path)
  let resolved ← try IO.FS.realPath absPath catch _ => pure absPath
  return System.Uri.pathToUri resolved

/-- Group `SerialMessage`s by file and convert to cross-file LSP diagnostics. -/
def serialMessagesToCrossFileDiagnostics (msgs : Array SerialMessage)
    : IO (Array (Lsp.DocumentUri × Array Lsp.Diagnostic)) := do
  let grouped := msgs.groupByKey (·.fileName)
  grouped.toArray.mapM fun (fileName, fileMsgs) => do
    let uri ← resolveFileUri fileName
    return (uri, fileMsgs.map serialMessageToDiagnostic)

/-- Uses `lake setup-file` to compile dependencies on the fly and add them to `LEAN_PATH`.
Compilation progress is reported to `handleStderr`. Returns the search path for
source files and the options for the file. -/
partial def setupFile (m : DocumentMeta) (header : ModuleHeader) (handleStderr : String → IO Unit) : IO FileSetupResult := do
  let some filePath := System.Uri.fileUriToPath? m.uri
    | return FileSetupResult.ofNoLakefile m header -- untitled files have no lakefile

  let lakePath ← determineLakePath
  if !(← System.FilePath.pathExists lakePath) then
    return FileSetupResult.ofNoLakefile m header

  let result ← runLakeSetupFile m lakePath filePath header handleStderr

  match result.exitCode with
  | 0 =>
    let Except.ok (setup : ModuleSetup) := Json.parse result.stdout >>= fromJson?
      | return ← FileSetupResult.ofError m header { summary := s!"Invalid lake setup-file output:\n{result.stdout}" }
    setup.dynlibs.forM loadDynlib
    FileSetupResult.ofSuccess setup
  | 2 => -- exit code for lake reporting that there is no lakefile
    return FileSetupResult.ofNoLakefile m header
  | 3 => -- exit code for `--no-build`
    FileSetupResult.ofImportsOutOfDate m header
  | _ =>
    let stdout := result.stdout.trimAsciiEnd.toString
    let err : LakeBuildError := (Json.parse stdout >>= fromJson?).toOption.getD {
      summary := if stdout.isEmpty then
        let stderr := result.stderr.trimAsciiEnd.toString
        if stderr.isEmpty then "lake setup-file failed" else stderr
      else stdout
    }
    FileSetupResult.ofError m header err
