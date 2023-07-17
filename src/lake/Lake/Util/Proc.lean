/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Lake.Util.Log

namespace Lake

@[specialize] def logProcCmd [Monad m]
(args : IO.Process.SpawnArgs) (log : String → m PUnit) : m Unit := do
  let envStr := String.join <| args.env.toList.map fun (k, v) =>
    if k == "PATH" then "PATH " else s!"{k}={v.getD ""} " -- PATH too big
  let cmdStr := " ".intercalate (args.cmd :: args.args.toList)
  log <| "> " ++ envStr ++
    match args.cwd with
    | some cwd => s!"{cmdStr}    # in directory {cwd}"
    | none     => cmdStr

@[specialize] def logProcOutput [Monad m]
(out : IO.Process.Output) (log : String → m PUnit) : m Unit := do
  unless out.stdout.isEmpty do
    log s!"stdout:\n{out.stdout}"
  unless out.stderr.isEmpty do
    log s!"stderr:\n{out.stderr}"

@[specialize] def logProcWith [Monad m]
(args : IO.Process.SpawnArgs) (out : IO.Process.Output)
(log : String → m PUnit) (logOutput := log) : m Unit := do
  logProcCmd args log
  logProcOutput out logOutput

def proc (args : IO.Process.SpawnArgs) (quiet := false) : LogIO Unit := do
  match (← IO.Process.output args |>.toBaseIO) with
  | .ok out =>
    if out.exitCode = 0 then
      logProcWith args out logVerbose (logOutput := if quiet then logVerbose else logInfo)
    else
      logProcWith args out logError
      error s!"external command `{args.cmd}` exited with code {out.exitCode}"
  | .error err =>
    error s!"failed to execute `{args.cmd}`: {err}"

def captureProc (args : IO.Process.SpawnArgs) : LogIO String := do
  match (← IO.Process.output args |>.toBaseIO) with
  | .ok out =>
    if out.exitCode = 0 then
      return out.stdout.trim -- remove, e.g., newline at end
    else
      logProcWith args out logError
      error s!"external command `{args.cmd}` exited with code {out.exitCode}"
  | .error err =>
    error s!"failed to execute `{args.cmd}`: {err}"

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
      stdout := IO.Process.Stdio.null
      stderr := IO.Process.Stdio.null
    }
    return (← child.wait) == 0
