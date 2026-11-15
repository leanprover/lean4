/-!
`IO.Process.output`, `IO.Process.run` and `IO.Process.binOutput` with input larger than a pipe
holds, children that do not read all of their input, and output that is not UTF-8 (#14000, #14001,
#14003).
-/
open IO.Process

def bigInput : String := String.ofList (List.replicate 1000000 'a')

/-! A child that writes while it reads gets input larger than a pipe holds (#14000). -/

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

/-- info: true -/
#guard_msgs in
#eval show IO Bool from do
  return (← run { cmd := "cat" } bigInput) == bigInput

/-! A child may exit without reading all of its input. -/

/-- info: 3 -/
#guard_msgs in
#eval show IO UInt32 from do
  return (← output { cmd := "sh", args := #["-c", "exit 3"] } bigInput).exitCode

/-- info: 3 -/
#guard_msgs in
#eval show IO UInt32 from do
  return (← output { cmd := "sh", args := #["-c", "head -c 10000 > /dev/null; exit 3"] } bigInput).exitCode

/-! Output that is not UTF-8 is reported only once the child has exited (#14001). -/

/-- info: ("process 'sh' wrote non-UTF-8 data to its standard error", true) -/
#guard_msgs in
#eval show IO (String × Bool) from do
  let start ← IO.monoMsNow
  let msg ← try
      discard <| output { cmd := "sh", args := #["-c", "printf '\\377' >&2; exec 2>&-; sleep 1"] }
      pure "no error"
    catch e => pure (toString e)
  -- Only a lower bound, with a margin in case `sleep` and `IO.monoMsNow` use different clocks.
  return (msg, (← IO.monoMsNow) - start ≥ 900)

/-- error: process 'sh' wrote non-UTF-8 data to its standard output -/
#guard_msgs in
#eval output { cmd := "sh", args := #["-c", "printf 'a\\377b'"] }

/-! `run` does not decode standard error strictly, since it only reports it on failure (#14003). -/

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

/-! `binOutput` captures output that is not UTF-8 as is (#14003). -/

/-- info: (0, #[97, 255, 98], #[255]) -/
#guard_msgs in
#eval show IO _ from do
  let out ← binOutput { cmd := "sh", args := #["-c", "printf 'a\\377b'; printf '\\377' >&2"] }
  return (out.exitCode, out.stdout.data, out.stderr.data)

/-- info: true -/
#guard_msgs in
#eval show IO Bool from do
  let input := ByteArray.mk <| (Array.range 1000000).map (·.toUInt8)
  let out ← binOutput { cmd := "cat" } input
  return out.exitCode == 0 && out.stdout == input && out.stderr.isEmpty
