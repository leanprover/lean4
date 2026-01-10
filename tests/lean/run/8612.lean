macro "assert_eq! " t1:term ", " t2:term : doElem =>
  `(doElem| if $t1 != $t2 then throw (.userError s!"{repr $t1} != {repr $t2}"))

macro "assert_failure! " e:doElem : doElem =>
  `(doElem| try $e; throw (.userError s!"unexpected success") catch _ => pure ())

def runTests : IO Unit := do
  unless System.Platform.isWindows do
    return
  let out ← IO.Process.run { cmd := "cmd.exe", args := #["/c", "echo", "hi"] }
  assert_eq! out, "hi\r\n"
  assert_failure! discard <| IO.Process.run { cmd := "cmd.exe\" echo \"hi" }
  assert_failure! discard <| IO.Process.run { cmd := "cmd.exe\\" }
  -- creating a lot of processes should succeed and not leak file handles
  for _ in [0:500] do
    discard <| IO.Process.run { cmd := "cmd.exe", args := #["/c", "echo", "hi"] }

#eval runTests
