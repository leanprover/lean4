/-!
Tests that a process spawned with `inheritEnv := false` gets exactly the environment variables set by
`env`. Previously, setting a variable this way made the child crash on macOS before it ran.
-/

def printenv (var : String) (env : Array (String × Option String)) : IO (UInt32 × String) := do
  let out ← IO.Process.output { cmd := "printenv", args := #[var], env, inheritEnv := false }
  return (out.exitCode, out.stdout.trimAsciiEnd.copy)

/-- info: (0, "1") -/
#guard_msgs in #eval printenv "TEST_VAR" #[("TEST_VAR", some "1")]

-- The parent's `PATH` is not inherited.
/-- info: (1, "") -/
#guard_msgs in #eval printenv "PATH" #[("TEST_VAR", some "1")]

/-- info: (1, "") -/
#guard_msgs in #eval printenv "TEST_VAR" #[("TEST_VAR", some "1"), ("TEST_VAR", none)]
