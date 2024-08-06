def test : IO Unit := do
  let tmpFile := "3546.tmp"
  let firstLine := "foo\u0000bar\n"
  let content := firstLine ++ "hello world\nbye"
  IO.FS.writeFile tmpFile content
  let handle ← IO.FS.Handle.mk tmpFile .read
  let firstReadLine ← handle.getLine
  let cond := firstLine == firstReadLine && firstReadLine.length == 8 -- paranoid
  IO.println cond
  IO.FS.removeFile tmpFile

/-- info: true -/
#guard_msgs in
#eval test
