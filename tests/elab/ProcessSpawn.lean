import Std.Internal.UV

/-!
Tests `IO.Process.spawn` and the operations on `IO.Process.Child`: spawn failures are reported as
`IO` errors, rejection of strings with NUL bytes, running executable files without a shebang via
`/bin/sh`, binary-safe pipes, exit codes of killed children, `kill` and `wait` after the child has
exited, reaping of dropped children, killing `setsid` process groups, environment construction,
argument passing and concurrent spawning.

The environment tests rely on `ProcessSpawn.lean.init.sh` exporting `LEAN_SPAWN_TEST_INHERITED`.
-/

open IO.Process

def check (cond : Bool) (msg : String) : IO Unit :=
  unless cond do throw <| IO.userError msg

def spawnError (args : SpawnArgs) : IO IO.Error := do
  match ← (spawn args).toBaseIO with
  | .ok child => throw <| IO.userError s!"spawn succeeded, the child exited with {← child.wait}"
  | .error e => return e

def missingCmd := "lean_process_spawn_missing_command"

/-! A command that cannot be executed fails `spawn` rather than the child. -/

/-- info: no such file or directory: lean_process_spawn_missing_command -/
#guard_msgs in
#eval show IO Unit from do
  match ← spawnError { cmd := missingCmd } with
  | .noFileOrDirectory file .. => IO.println s!"no such file or directory: {file}"
  | e => throw e

/-- info: no such file or directory: lean_process_spawn_missing_dir -/
#guard_msgs in
#eval show IO Unit from do
  match ← spawnError { cmd := "sh", args := #["-c", "exit 0"], cwd := "lean_process_spawn_missing_dir" } with
  | .noFileOrDirectory file .. => IO.println s!"no such file or directory: {file}"
  | e => throw e

#eval show IO Unit from do
  if System.Platform.isWindows then return
  IO.FS.withTempDir fun dir => do
    let script := dir / "script.sh"
    IO.FS.writeFile script "#!/bin/sh\nexit 0\n"
    IO.setAccessRights script { user := { read := true, write := true } }
    match ← spawnError { cmd := script.toString } with
    | .permissionDenied (some file) .. => check (file == script.toString) s!"wrong file {file}"
    | e => throw e

/-! Strings containing NUL bytes are rejected rather than truncated. -/

/--
info: "sh\x00x"
"a\x00b"
"x\x00"
"LEAN_SPAWN_TEST\x00X"
"v\x00w"
"LEAN_SPAWN_TEST\x00X"
-/
#guard_msgs in
#eval show IO Unit from do
  let sh : SpawnArgs := { cmd := "sh", args := #["-c", "exit 0"] }
  for args in [{ sh with cmd := "sh\x00x" }, { sh with args := sh.args.push "a\x00b" },
      { sh with cwd := some "x\x00" }, { sh with env := #[("LEAN_SPAWN_TEST\x00X", some "v")] },
      { sh with env := #[("LEAN_SPAWN_TEST_X", some "v\x00w")] },
      { sh with env := #[("LEAN_SPAWN_TEST\x00X", none)] }] do
    match ← spawnError args with
    | .invalidArgument (some s) .. => IO.println (repr s)
    | e => throw e

/-! Executable files without a shebang are run by `/bin/sh`, as `execvp` does. -/

#eval show IO Unit from do
  if System.Platform.isWindows then return
  IO.FS.withTempDir fun dir => do
    let name := "lean_spawn_test_script"
    let writeScript (file : System.FilePath) (code : Nat) : IO Unit := do
      IO.FS.writeFile file s!"printf '%s|' \"$@\"\nexit {code}\n"
      IO.setAccessRights file { user := { read := true, write := true, execution := true } }
    let script := dir / name
    writeScript script 7
    let run (args : SpawnArgs) (code : UInt32) (what : String) : IO Unit := do
      let out ← output { args with args := #["a b", "c"] }
      check (out.exitCode == code && out.stdout == "a b|c|") s!"{what}: {out.exitCode} {repr out.stdout} {out.stderr}"
    run { cmd := script.toString } 7 "absolute path"
    run { cmd := s!"./{name}", cwd := dir } 7 "relative to `cwd`"
    let path := s!"{dir}:{(← IO.getEnv "PATH").getD ""}"
    run { cmd := name, env := #[("PATH", some path)] } 7 "`PATH` lookup"
    -- A relative `PATH` entry is resolved against the child's working directory, which comes first.
    IO.FS.createDir (dir / "sub")
    writeScript (dir / "sub" / name) 8
    run { cmd := name, cwd := dir / "sub", env := #[("PATH", some s!".:{path}")] } 8 "relative `PATH` entry"

/-! Pipes carry bytes unchanged, with no line ending or end-of-file translation on Windows. -/

#eval show IO Unit from do
  let bytes : ByteArray := ⟨#[97, 13, 10, 98, 26, 99, 10, 0, 255, 13]⟩
  let out ← binOutput { cmd := "cat" } (input? := some bytes)
  check (out.exitCode == 0 && out.stdout.data == bytes.data) s!"`cat` returned {out.stdout.data}"

/-! Failed spawns leave the event loop intact. -/

#eval show IO Unit from do
  for _ in [0:200] do
    discard <| spawnError { cmd := missingCmd }
    let timer ← Std.Internal.UV.Timer.mk 0 false
    discard <| timer.next
    timer.stop
  check ((← (← spawn { cmd := "sh", args := #["-c", "exit 5"] }).wait) == 5) "spawn after failures"

/-! Exit codes. -/

#eval show IO Unit from do
  let child ← spawn { cmd := "cat", stdin := .piped }
  check ((← child.tryWait) == none) "`cat` exited before its stdin was closed"
  child.kill
  let code ← child.wait
  -- `TerminateProcess` on Windows; 128 + `SIGKILL` elsewhere
  check (code == if System.Platform.isWindows then 1 else 137) s!"the killed child exited with {code}"

#eval show IO Unit from do
  if System.Platform.isWindows then return
  let code ← (← spawn { cmd := "sh", args := #["-c", "kill -TERM $$"] }).wait
  check (code == 143) s!"the child killed by `SIGTERM` exited with {code}"

#eval show IO Unit from do
  unless System.Platform.isWindows do return
  let code ← (← spawn { cmd := "cmd.exe", args := #["/c", "exit 1000"] }).wait
  check (code == 1000) s!"`exit 1000` exited with {code}"

/-! `wait`, `tryWait` and `kill` keep working once the child has exited and been reaped. -/

#eval show IO Unit from do
  let child ← spawn { cmd := "sh", args := #["-c", "exit 3"] }
  check ((← child.wait) == 3) "first `wait`"
  check ((← child.wait) == 3) "second `wait`"
  check ((← child.tryWait) == some 3) "`tryWait` after `wait`"
  child.kill
  check ((← child.wait) == 3) "`wait` after `kill`"

/-! The pid is the child's. -/

#eval show IO Unit from do
  if System.Platform.isWindows then return
  let child ← spawn { cmd := "sh", args := #["-c", "echo $$"], stdout := .piped }
  let out ← child.stdout.readToEnd
  check (out.trimAscii.copy == toString child.pid) s!"the child reports pid {out}, not {child.pid}"
  discard child.wait

/-! A child that is dropped without waiting for it is still reaped, rather than left a zombie. -/

#eval show IO Unit from do
  unless System.Platform.isLinux do return
  let mut pids := #[]
  for _ in [0:20] do
    let child ← spawn { cmd := "sh", args := #["-c", "exit 0"] }
    pids := pids.push child.pid
  for pid in pids do
    let stat : System.FilePath := s!"/proc/{pid}/stat"
    let mut reaped := false
    for _ in [0:100] do
      unless ← stat.pathExists do
        reaped := true
        break
      IO.sleep 100
    check reaped s!"the dropped child {pid} was not reaped"

/-! `kill` on a `setsid` child kills its process group, also once the leader has exited. -/

/-- Waits for the last process holding the write end of `h`'s pipe to exit. -/
def waitForEof (h : IO.FS.Handle) (what : String) : IO Unit := do
  let t ← IO.asTask h.readToEnd .dedicated
  for _ in [0:100] do
    if ← IO.hasFinished t then
      discard <| IO.ofExcept t.get
      return
    IO.sleep 100
  throw <| IO.userError s!"{what} was not killed"

#eval show IO Unit from do
  if System.Platform.isWindows then return
  let child ← spawn {
    cmd := "sh", args := #["-c", "sleep 30 & echo started; wait"], stdout := .piped, setsid := true }
  check ((← child.stdout.getLine) == "started\n") "`sleep` was not started"
  child.kill
  check ((← child.wait) == 137) "the leader was not killed"
  waitForEof child.stdout "`sleep`"

#eval show IO Unit from do
  if System.Platform.isWindows then return
  -- The leader exits right away, leaving `sleep` and the pipe behind in its process group.
  let child ← spawn { cmd := "sh", args := #["-c", "sleep 30 &"], stdout := .piped, setsid := true }
  check ((← child.wait) == 0) "the leader failed"
  child.kill
  waitForEof child.stdout "the orphaned `sleep`"

-- `setsid` is a no-op on Windows
#eval show IO Unit from do
  check ((← (← spawn { cmd := "sh", args := #["-c", "exit 4"], setsid := true }).wait) == 4) "setsid"

/-! Environment. -/

def inherited := "LEAN_SPAWN_TEST_INHERITED"

def printenv (var : String) (env : Array (String × Option String) := #[]) (inheritEnv := true) :
    IO (Option String) := do
  let out ← output { cmd := "printenv", args := #[var], env, inheritEnv }
  return if out.exitCode == 0 then some out.stdout.trimAsciiEnd.copy else none

/--
info: some "parent"
some "child"
none
none
some "2"
none
some "1"
-/
#guard_msgs in
#eval show IO Unit from do
  check ((← IO.getEnv inherited) == some "parent") s!"{inherited} is not set, run this via the test suite"
  IO.println (repr (← printenv inherited))
  IO.println (repr (← printenv inherited (env := #[(inherited, some "child")])))
  IO.println (repr (← printenv inherited (env := #[(inherited, none)])))
  -- processed from left to right
  let x := "LEAN_SPAWN_TEST_X"
  IO.println (repr (← printenv x (env := #[(x, some "1"), (x, none)])))
  IO.println (repr (← printenv x (env := #[(x, none), (x, some "2")])))
  let path := #[("PATH", ← IO.getEnv "PATH")]
  IO.println (repr (← printenv inherited (env := path) (inheritEnv := false)))
  IO.println (repr (← printenv x (env := path.push (x, some "1")) (inheritEnv := false)))

-- Windows compares variable names case-insensitively
#eval show IO Unit from do
  unless System.Platform.isWindows do return
  let v ← printenv inherited (env := #[(inherited.toLower, some "child")])
  check (v == some "child") s!"overriding with a lowercase name gave {repr v}"

/-! Arguments reach the child verbatim. -/

def argsSource : String := "def main (args : List String) : IO Unit := IO.println (repr args.toArray)"

#eval show IO Unit from do
  let mut args := #["plain", "a b", "\"quoted\"", "", "back\\slash\\", "a\\\"b", "tab\there", "x=y"]
  unless System.Platform.isWindows do
    args := args ++ #["ü", "new\nline"]
  IO.FS.withTempDir fun dir => do
    let file := dir / "args.lean"
    IO.FS.writeFile file argsSource
    let out ← output { cmd := (← IO.appPath).toString, args := #["--run", file.toString] ++ args }
    check (out.exitCode == 0) s!"`lean --run` failed:\n{out.stderr}"
    check (out.stdout.trimAsciiEnd.copy == toString (repr args)) s!"the child got {out.stdout}"

/-! Concurrent spawns from many threads. -/

#eval show IO Unit from do
  let tasks ← (List.range 32).mapM fun i => IO.asTask (prio := .dedicated) do
    if i % 4 == 0 then
      discard <| spawnError { cmd := missingCmd }
    let out ← output { cmd := "cat" } (input? := some s!"line {i}\n")
    check (out.exitCode == 0 && out.stdout == s!"line {i}\n") s!"task {i} got {repr out.stdout}"
  for t in tasks do
    IO.ofExcept t.get
