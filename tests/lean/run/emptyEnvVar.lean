/--
Tests that spawning a process with a environment variable configured to the
empty string correctly sets the environment variable on the subprocess on
all platforms. Previously, this was broken on Windows.
-/
def test : IO String := do
  let var := "TEST_VAR"
  let out ← IO.Process.output {
    cmd := "printenv"
    args := #[var]
    env := #[(var, some "")]
  }
  unless out.exitCode == 0 do
    throw <| .userError "environment variable not set"
  return out.stdout.trimAsciiEnd.copy -- trim ending newline

/-- info: "" -/
#guard_msgs in #eval test
