/-
Copyright (c) 2026 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lake.Util.Log
import Init.Data.String.TakeDrop
import Init.Data.String.Lossy

set_option doc.verso true

/-!
# Subprocess Execution

An API for spawning subprocesses inspired by Rust's [Command][1].

[1]: https://doc.rust-lang.org/std/process/struct.Command.html
-/

namespace Lake

namespace Subprocess

inductive Input
| none
| str (v : String)
| bin (v : ByteArray)

/-- The exit code of a subprocess. -/
public abbrev ExitStatus := UInt32

structure Impl where
  spawnArgs : IO.Process.SpawnArgs
  input : Input := .none

end Subprocess

/-- A subprocess to spawn. -/
public structure Subprocess where
  private mk ::
    private impl : Subprocess.Impl

namespace Subprocess

/-! ## Construction -/

/-- Constructs a subprocess from a command name. -/
@[inline] public def ofCommand (cmd : String) : Subprocess :=
  ⟨{spawnArgs := {cmd, stdin := .null, stderr := .piped, stdout := .piped}}⟩

/-- Constructs a subprocess from an executable file path. -/
@[inline] public def ofFilePath (path : System.FilePath) : Subprocess :=
   ofCommand path.toString

/-- Constructs a subprocess from a {lean}`IO.Process.SpawnArgs` description. -/
@[inline] public def ofSpawnArgs (args : IO.Process.SpawnArgs) : Subprocess :=
  ⟨{spawnArgs := args}⟩

/-- Converts the subprocess description into its {lean}`IO.Process.SpawnArgs`. -/
@[inline] public def toSpawnArgs (self : Subprocess) : IO.Process.SpawnArgs :=
  self.impl.spawnArgs

/-! ## Configuration -/

/-- Sets the working directory of the subprocess to {lean}`path`. -/
@[inline] public def withCwd (path : System.FilePath) (self : Subprocess) : Subprocess :=
  {self with impl.spawnArgs.cwd := path}

/-- Sets the subprocess argument list to {lean}`args`. -/
@[inline] public def withArgs (args : Array String) (self : Subprocess) : Subprocess :=
  {self with impl.spawnArgs.args := args}

/-- Applies {lean}`f` to subprocess argument list. -/
@[inline] public def modifyArgs (f : Array String → Array String) (self : Subprocess) : Subprocess :=
  {self with impl.spawnArgs.args := f self.impl.spawnArgs.args}

/-- Appends {lean}`arg` to the subprocess argument list. -/
@[inline] public def addArg (arg : String) (self : Subprocess) : Subprocess :=
  self.modifyArgs (·.push arg)

/-- Appends {lean}`arg` to the subprocess argument list if {lean}`cond` is {lean}`true`. -/
@[inline] public def addArgIf (cond : Bool) (arg : String) (self : Subprocess) : Subprocess :=
  if cond then self.addArg arg else self

/-- Appends {lean}`args` to the subprocess argument list. -/
@[inline] public def addArgs (args : Array String) (self : Subprocess) : Subprocess :=
  self.modifyArgs (· ++ args)

/-- Adds or removes enviroment variables from the subprocess. See {lean}`IO.Process.SpawnArgs.env`. -/
@[inline] public def withEnv (env : Array (String × Option String)) (self : Subprocess) : Subprocess :=
  {self with impl.spawnArgs.env := env}

/-- Clears the subprocess environment and stops it inheriting parent process environment variables. -/
@[inline] public def withoutEnv (self : Subprocess) : Subprocess :=
  {self with impl.spawnArgs.env := #[], impl.spawnArgs.inheritEnv := false}

/-- Prevents the subprocess from inheriting the enviroment variable {lean}`var` from its parent. -/
@[inline] public def clearEnvVar (var : String) (self : Subprocess) : Subprocess :=
  {self with impl.spawnArgs.env := self.impl.spawnArgs.env.push (var, none)}

/-- Sets the variable {lean}`var` to {lean}`val` in the subprocess environment. -/
@[inline] public def addEnvVar (var : String) (val : String) (self : Subprocess) : Subprocess :=
  {self with impl.spawnArgs.env := self.impl.spawnArgs.env.push (var, some val)}

/--
Sets the variable {lean}`var` to {lean}`val` in the subprocess environment
if {lean}`cond` is {lean}`true`.
-/
@[inline] public def addEnvVarIf (cond : Bool) (var : String) (val : String) (self : Subprocess) : Subprocess :=
  if cond then self.addEnvVar var val else self

/--
Sets the variable {lean}`var` to {lean}`val?` in the subprocess environment
if {lean}`val?` is not {lean}`none`.

Unlike {lean}`IO.Process.SpawnArgs.env`, a {lean}`none` value does NOT prevent
inherting {lean}`var` from the parent process.
-/
@[inline] public def addEnvVarIfSome (var : String) (val? : Option String) (self : Subprocess) : Subprocess :=
  val?.elim self fun val => self.addEnvVar var val

/-- Streams {lean}`input` to the subprocess over standard input. -/
@[inline] public def withStrInput (input : String) (self : Subprocess) : Subprocess :=
  {self with impl.spawnArgs.stdin := .piped, impl.input := .str input}

/-- Streams {lean}`input` to the subprocess over standard input. -/
@[inline] public def withBinInput (input : ByteArray) (self : Subprocess) : Subprocess :=
  {self with impl.spawnArgs.stdin := .piped, impl.input := .bin input}

/-- Configures the standard input stream of the subprocess. -/
@[inline] public def withStdin (stdin : IO.Process.Stdio) (self : Subprocess) : Subprocess :=
  {self with impl.spawnArgs.stdin := stdin}

/-- Configures the stadnard output stream of the subprocess. -/
@[inline] public def withStdout (stdout : IO.Process.Stdio) (self : Subprocess) : Subprocess :=
  {self with impl.spawnArgs.stdout := stdout}

/-- Configures the atandard error stream of the subprocess. -/
@[inline] public def withStderr (stderr : IO.Process.Stdio) (self : Subprocess) : Subprocess :=
  {self with impl.spawnArgs.stderr := stderr}

/-! ## Execution -/

/-- A spawned subprocess. -/
public abbrev Child (self : Subprocess) :=
  IO.Process.Child self.toSpawnArgs.toStdioConfig

/-- Propositional variant of {lean}`IO.Process.Child.takeStdin`. -/
public nonrec def Child.takeStdin
  (proc : Subprocess) (child : proc.Child) (h : proc.toSpawnArgs.stdin = .piped)
: IO (IO.FS.Handle × IO.Process.Child { proc.toSpawnArgs with stdin := .null }) :=
  cast (by simp [h, IO.Process.Stdio.toHandleType]) child.takeStdin

/-- Propositional variant of {lean}`IO.Process.Child.stdout`. -/
public nonrec def Child.stdout (proc : Subprocess) (child : proc.Child) (h : proc.toSpawnArgs.stdout = .piped) : IO.FS.Handle :=
  cast (by simp [h, IO.Process.Stdio.toHandleType]) child.stdout

/-- Propositional variant of {lean}`IO.Process.Child`. -/
public nonrec def Child.stderrt (proc : Subprocess) (child : proc.Child) (h : proc.toSpawnArgs.stderr = .piped) : IO.FS.Handle :=
  cast (by simp [h, IO.Process.Stdio.toHandleType]) child.stderr

/-- Spawns the subprocess, returning a hanlde to the child. -/
@[inline] public def spawn (self : Subprocess) : IO self.Child :=
  IO.Process.spawn self.impl.spawnArgs

def binOutputAsync (args : IO.Process.SpawnArgs) (input : Input) : BaseIO (Task (Except String IO.Process.BinOutput)) := do
  -- Adapted from `binOutput` in `Init.IO`
  let (child, written) ← do
    if h : input matches .none then
      let args := { args with stdin := .null }
      match (← IO.Process.spawn args |>.toBaseIO) with
      | .ok child => pure (child, Task.pure (.ok ()))
      | .error e => return Task.pure <| .error s!"failed to spawn subprocess: {e}"
    else
      match (← IO.Process.spawn { args with stdin := .piped } |>.toBaseIO) with
      | .ok child =>
        match (← child.takeStdin.toBaseIO) with
        | .ok (stdin, child) =>
          -- The task holds the only reference to `stdin`,
          -- so the child sees the end of its input when the task finishes.
          let written ← IO.asTask (prio := .dedicated) do
            try
              match h_eq:input with
              | .str v => stdin.putStr v
              | .bin v => stdin.write v
              | .none => h.elim (by simp [h_eq])
              stdin.flush
            catch e =>
              match e with
              -- The child exited or closed its standard input early.
              -- Windows reports this as `EINVAL` rather than `EPIPE`.
              | .resourceVanished .. | .invalidArgument .. => pure ()
              | e => throw e
          pure (child, written)
        | .error e =>
          return Task.pure <| .error s!"failed to obtain subprocess stdin: {e}"
      | .error e =>
        return Task.pure <| .error s!"failed to spawn subprocess: {e}"
  let stdout ←
    match args, child with
    | {stdout := .piped, ..}, child => IO.asTask (prio := .dedicated) child.stdout.readBinToEnd
    | _, _ => pure <| Task.pure (.ok ByteArray.empty)
  EIO.bindTask (sync := true) written fun
    | .ok () => do
      let stderr ←
        match args, child with
        | {stderr := .piped, ..}, child => child.stderr.readBinToEnd.toBaseIO
        | _, _ => pure (.ok ByteArray.empty)
      EIO.mapTask (sync := true) (t := stdout) fun stdout => do
        match stdout with
        | .ok stdout =>
          match stderr with
          | .ok stderr =>
            match (← child.wait |>.toBaseIO) with
            | .ok exitCode => return {exitCode, stdout, stderr}
            | .error e => throw s!"failed to wait on subprocess: {e}"
          | .error e =>  throw s!"failed to read subprocess stderr: {e}"
        | .error e => throw s!"failed to read subprocess stdout: {e}"
    | .error e =>
      return Task.pure <| .error s!"failed to write subprocess stdin: {e}"

def mkSpawnMessage (args : IO.Process.SpawnArgs)
  (caption : String := "subprocess completed successfully")
: BaseIO String := do
  let cmd := " ".intercalate (args.cmd :: args.args.toList)
  let mut msg := s!"{caption}\n  {cmd}"
  let cwd := args.cwd.getD "."
  let cwd := (← IO.FS.realPath cwd |>.toBaseIO).toOption.getD cwd
  msg := s!"{msg}\ncwd: {cwd}"
  unless args.env.isEmpty do
    msg := args.env.foldl (init := s!"{msg}env:") fun msg (var, val?) =>
      if let some val := val? then s!"\n {var}={val}" else msg
  return msg

def mkMessage (args : IO.Process.SpawnArgs) (out : IO.Process.BinOutput)
  (caption : String := "subprocess completed successfully")
: BaseIO String := do
  let mut msg ← mkSpawnMessage args s!"{caption} (exit code: {out.exitCode})"
  unless out.stdout.isEmpty do
    msg := s!"{msg}\nstdout:\n{String.fromUTF8Lossy out.stdout}"
  unless out.stderr.isEmpty do
    msg := s!"{msg}\nstderr:\n{String.fromUTF8Lossy out.stderr}"
  return msg

def checkExit (args : IO.Process.SpawnArgs) (out : IO.Process.BinOutput) : LogIO Unit :=
  unless out.exitCode == 0 do
    error <| ← mkMessage args out s!"subprocess did not complete successfully"

def binOutputSync (args : IO.Process.SpawnArgs) (input : Input) : LogIO IO.Process.BinOutput := do
  let outTask ← binOutputAsync args input
  match (← IO.wait outTask) with
  | .ok out =>
    return out
  | .error e =>
    error (← mkSpawnMessage args e)

/-- Runs the subprocess and returns its results, interpreting its output streams as bytes. -/
@[inline] public def binOutput (self : Subprocess) : LogIO IO.Process.BinOutput := do
  let args := {self.impl.spawnArgs with stdout := .piped, stderr := .piped}
  let out ← binOutputSync args self.impl.input
  logVerbose (← mkSpawnMessage args s!"subprocess exited with code {out.exitCode}")
  return out

/--
Runs the subprocess and returns its results, interpreting its output streams as bytes.

Errors if the subprocess does not complete with exit code {lean}`0`.
-/
@[inline] public def binOutputwithSuccess (self : Subprocess) : LogIO IO.Process.BinOutput := do
  let args := {self.impl.spawnArgs with stdout := .piped, stderr := .piped}
  let out ← binOutputSync args self.impl.input
  checkExit args out
  logVerbose (← mkSpawnMessage args s!"subprocess exited with code {out.exitCode}")
  return out

def mkStrOutput (args : IO.Process.SpawnArgs) (out : IO.Process.BinOutput) : LogIO IO.Process.Output := do
  let some stdout := String.fromUTF8? out.stdout
    | error <| ← mkMessage args out "subprocess produced non-UTF8 output on stdout"
  let some stderr := String.fromUTF8? out.stderr
    | error <| ← mkMessage args out "subprocess produced non-UTF8 output on stderr"
  return {exitCode := out.exitCode, stdout, stderr}

/-- Runs the subprocess and returns its results, interpreting its output streams as UTF-8. -/
@[inline] public def strOutput (self : Subprocess) : LogIO IO.Process.Output := do
  let args := {self.impl.spawnArgs with stdout := .piped, stderr := .piped}
  let out ← binOutputSync args self.impl.input
  logVerbose (← mkSpawnMessage args s!"subprocess exited with code {out.exitCode}")
  mkStrOutput args out

/--
Runs the subprocess and returns its results, interpreting its output streams as UTF-8.

Errors if the subprocess does not complete with exit code {lean}`0`.
-/
@[inline] public def strOutputwithSuccess (self : Subprocess) : LogIO IO.Process.Output := do
  let args := {self.impl.spawnArgs with stdout := .piped, stderr := .piped}
  let out ← binOutputSync args self.impl.input
  checkExit args out
  logVerbose (← mkSpawnMessage args s!"subprocess exited with code {out.exitCode}")
  mkStrOutput args out

/-- Runs the subprocess and returns its exit code. -/
@[inline] public def status (self : Subprocess) : LogIO ExitStatus := do
  let args := self.impl.spawnArgs
  let out ←  binOutputSync self.impl.spawnArgs self.impl.input
  logVerbose (← mkMessage args out)
  return out.exitCode

/--
Runs the subprocess. Errors if it does not complete with exit code {lean}`0`.
-/
public def run (self : Subprocess) : LogIO Unit := do
  let args := self.impl.spawnArgs
  let out ← binOutputSync args self.impl.input
  checkExit args out
  logVerbose (← mkMessage args out)

/--
Runs the subprocess and returns {lean}`true` if it completes with exit code {lean}`0`.

Returns {lean}`false` if executing the process fails or it exits non-zero.
-/
public def tryRun (self : Subprocess) : BaseIO Bool := do
  let args := {self.impl.spawnArgs with stdout := .null, stderr := .null}
  let outTask ← binOutputAsync args self.impl.input
  let .ok out ← IO.wait outTask
    | return false
  return out.exitCode == 0

/--
Runs the subprocess and returns its captured standard output as trimmed UTF-8.

Errors if the subprocess does not complete with exit code {lean}`0` or
if it produces non-UTF8 output.
-/
public def capture (self : Subprocess) : LogIO String := do
  let args := self.impl.spawnArgs
  let out ← binOutputSync args self.impl.input
  checkExit args out
  let some stdout := String.fromUTF8? out.stdout
    | error <| ← mkMessage args out "subprocess produced non-UTF8 output on stdout"
  logVerbose (← mkSpawnMessage args s!"subprocess exited with code {out.exitCode}")
  return stdout.trimAscii.copy -- remove, e.g., newline at end

/--
Runs the subprocess and returns its captured standard output as trimmed UTF-8.

Returns {lean}`none` if the subprocess does not complete with exit code {lean}`0` or
if it produces non-UTF8 output.
-/
public def tryCapture? (self : Subprocess) : BaseIO (Option String) := do
  let args := {self.impl.spawnArgs with stdout := .piped, stderr := .piped}
  let outTask ← binOutputAsync args self.impl.input
  let .ok out ← IO.wait outTask
    | return none
  unless out.exitCode == 0 do
    return none
  let some stdout := String.fromUTF8? out.stdout
    | return none
  return some stdout.trimAscii.copy -- remove, e.g., newline at end
