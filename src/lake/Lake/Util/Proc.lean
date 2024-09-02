/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Lake.Util.Log

namespace Lake

def mkCmdLog (args : IO.Process.SpawnArgs) : String :=
  let envStr := String.join <| args.env.toList.map fun (k, v) =>
    if k == "PATH" then "PATH " else s!"{k}={v.getD ""} " -- PATH too big
  let cmdStr := " ".intercalate (args.cmd :: args.args.toList)
  let cwd := args.cwd.getD "."
  s!"{cwd}> {envStr}{cmdStr}"

@[inline] def logOutput
  [Monad m] (out : IO.Process.Output) (log : String → m PUnit)
: m Unit := do
  unless out.stdout.isEmpty do
    log s!"stdout:\n{out.stdout}"
  unless out.stderr.isEmpty do
    log s!"stderr:\n{out.stderr}"

@[inline] def rawProc (args : IO.Process.SpawnArgs) (quiet := false) : LogIO IO.Process.Output := do
  withLogErrorPos do
  unless quiet do logVerbose (mkCmdLog args)
  match (← IO.Process.output args |>.toBaseIO) with
  | .ok out => return out
  | .error err => error s!"failed to execute '{args.cmd}': {err}"

def proc (args : IO.Process.SpawnArgs) (quiet := false) : LogIO Unit := do
  withLogErrorPos do
  let out ← rawProc args
  logOutput out (if quiet then logVerbose else logInfo)
  if out.exitCode ≠ 0 then
    error s!"external command '{args.cmd}' exited with code {out.exitCode}"

def captureProc (args : IO.Process.SpawnArgs) : LogIO String := do
  let out ← rawProc args (quiet := true)
  if out.exitCode = 0 then
    return out.stdout.trim -- remove, e.g., newline at end
  else errorWithLog do
    logVerbose (mkCmdLog args)
    logOutput out logInfo
    logError s!"external command '{args.cmd}' exited with code {out.exitCode}"

def captureProc? (args : IO.Process.SpawnArgs) : BaseIO (Option String) := do
  EIO.catchExceptions (h := fun _ => pure none) do
    let out ← IO.Process.output args
    if out.exitCode = 0 then
      return some out.stdout.trim -- remove, e.g., newline at end
    else
      return none

def testProc (args : IO.Process.SpawnArgs) : BaseIO Bool :=
  EIO.catchExceptions (h := fun _ => pure false) do
    let child ← IO.Process.spawn {
      args with
      stdin := IO.Process.Stdio.null
      stdout := IO.Process.Stdio.null
      stderr := IO.Process.Stdio.null
    }
    return (← child.wait) == 0
