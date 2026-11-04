/-!
`IO.Process.output` and `IO.Process.run` with large input, a child that exits without reading its
input, and output that is not UTF-8 (issues #14000, #14001 and #14003).
-/
open IO.Process

def bigInput : String := String.ofList (List.replicate 1000000 'a')

/-! Input larger than a pipe holds reaches a child that writes its output while it reads (#14000). -/

/-- info: true -/
#guard_msgs in
#eval show IO Bool from do
  let out ← output { cmd := "cat" } bigInput
  return out.exitCode == 0 && out.stdout == bigInput && out.stderr == ""

/-- info: true -/
#guard_msgs in
#eval show IO Bool from do
  let out ← output { cmd := "sh", args := #["-c", "cat >&2"] } bigInput
  return out.exitCode == 0 && out.stdout == "" && out.stderr == bigInput

/-! A child may exit without reading all of its input. -/

/-- info: 3 -/
#guard_msgs in
#eval show IO UInt32 from do
  let out ← output { cmd := "sh", args := #["-c", "exit 3"] } bigInput
  return out.exitCode

/-- info: 3 -/
#guard_msgs in
#eval show IO UInt32 from do
  let out ← output { cmd := "sh", args := #["-c", "head -c 10000 > /dev/null; exit 3"] } bigInput
  return out.exitCode

/-!
Output that is not UTF-8 is reported only once the child has exited, not while it still runs
(#14001). The child closes its standard error early and then sleeps for a second. The elapsed time
is checked only from below, with a margin in case `sleep` and `IO.monoMsNow` use different clocks.
-/

/-- info: ("process 'sh' wrote non-UTF-8 data to its standard error", true) -/
#guard_msgs in
#eval show IO (String × Bool) from do
  let start ← IO.monoMsNow
  let msg ← try
      discard <| output { cmd := "sh", args := #["-c", "printf '\\377' >&2; exec 2>&-; sleep 1"] }
      pure "no error"
    catch e => pure (toString e)
  return (msg, (← IO.monoMsNow) - start ≥ 900)

/-- error: process 'sh' wrote non-UTF-8 data to its standard output -/
#guard_msgs in
#eval output { cmd := "sh", args := #["-c", "printf 'a\\377b'"] }

/-! `run` does not need the standard error of a successful child to be UTF-8 (#14003). -/

/-- info: "out\n" -/
#guard_msgs in
#eval run { cmd := "sh", args := #["-c", "printf '\\377' >&2; echo out"] }

/--
error: process 'sh' exited with code 1
stderr:
a�b
-/
#guard_msgs in
#eval run { cmd := "sh", args := #["-c", "printf 'a\\377b' >&2; exit 1"] }

/-- error: process 'sh' wrote non-UTF-8 data to its standard output -/
#guard_msgs in
#eval run { cmd := "sh", args := #["-c", "printf 'a\\377b'"] }
