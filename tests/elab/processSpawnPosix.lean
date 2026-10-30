/-!
`IO.Process.spawn` goes through `posix_spawn` on Unix (previously `fork` + `exec`). These checks pin down the
semantics the two implementations must agree on: inherited and private environments with `set`/`unset`
entries applied in order, `cwd`, the three stdio modes, `setsid`, and the failure of a command that cannot
be executed.
-/

def run (args : IO.Process.SpawnArgs) : IO String := do
  let out ← IO.Process.output args
  unless out.exitCode == 0 do
    throw <| .userError s!"exit code {out.exitCode}: {out.stderr}"
  return out.stdout.trimAsciiEnd.copy

/-- An inherited variable, an overridden one, a new one and an unset one, in one spawn. -/
def envTest : IO String := do
  let out ← run {
    cmd := "sh"
    args := #["-c", "echo \"${LEAN_SPAWN_A-unsetA}|${LEAN_SPAWN_B-unsetB}|${LEAN_SPAWN_C-unsetC}|${PATH:+path}\""]
    env := #[("LEAN_SPAWN_A", some "a"), ("LEAN_SPAWN_B", some "b"), ("LEAN_SPAWN_B", none), ("LEAN_SPAWN_C", some "")]
  }
  return out

/-- info: "a|unsetB||path" -/
#guard_msgs in #eval envTest

/-- A later entry for the same variable wins. -/
def envOrderTest : IO String := run {
  cmd := "sh", args := #["-c", "echo \"$LEAN_SPAWN_A\""]
  env := #[("LEAN_SPAWN_A", some "first"), ("LEAN_SPAWN_A", some "second")]
}

/-- info: "second" -/
#guard_msgs in #eval envOrderTest

/-- Without `inheritEnv`, only the given entries exist (`PATH` is needed to find `sh`; a shell may add a
few variables of its own, so a variable that is always inherited otherwise is checked instead of the whole
environment). -/
def privateEnvTest : IO String := run {
  cmd := "/bin/sh", args := #["-c", "echo \"${LEAN_SPAWN_ONLY-unset}|${HOME-unset}|${LEAN_SPAWN_A-unset}\""]
  env := #[("LEAN_SPAWN_ONLY", some "1")]
  inheritEnv := false
}

/-- info: "1|unset|unset" -/
#guard_msgs in #eval privateEnvTest

def cwdTest : IO Bool := do
  let out ← run { cmd := "pwd", cwd := some "/" }
  return out == "/"

/-- info: true -/
#guard_msgs in #eval cwdTest

/-- `null` stdio: no input to read, no output seen by the parent. -/
def nullStdioTest : IO (UInt32 × String) := do
  let child ← IO.Process.spawn {
    cmd := "sh", args := #["-c", "cat; echo out; echo err >&2"]
    stdin := .null, stdout := .null, stderr := .null
  }
  let rc ← child.wait
  let out ← run { cmd := "sh", args := #["-c", "cat; echo only"], stdin := .null }
  return (rc, out)

/-- info: (0, "only") -/
#guard_msgs in #eval nullStdioTest

/-- A command that cannot be executed fails either at `spawn` (an `IO.Error`) or in the child (exit code 255). -/
def execFailureTest : IO String := do
  try
    let child ← IO.Process.spawn { cmd := "/nonexistent/lean-spawn-test", stderr := .null }
    let rc ← child.wait
    return if rc == 255 then "failed" else s!"unexpected exit code {rc}"
  catch _ =>
    return "failed"

/-- info: "failed" -/
#guard_msgs in #eval execFailureTest

/-- With `setsid`, the child is the leader of a new session (checked with `ps` on Linux, whose `sid` column
is portable there; elsewhere the check is skipped). -/
def setsidTest : IO String := do
  let uname ← run { cmd := "uname" }
  unless uname == "Linux" do return "ok"
  let out ← run { cmd := "/bin/sh", args := #["-c", "ps -o sid= -p $$ | tr -d ' '; ps -o pid= -p $$ | tr -d ' '"], setsid := true }
  match out.splitOn "\n" with
  | [sid, pid] => return if sid == pid then "ok" else s!"sid {sid} ≠ pid {pid}"
  | _ => return s!"unexpected output {repr out}"

/-- info: "ok" -/
#guard_msgs in #eval setsidTest
