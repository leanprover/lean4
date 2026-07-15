def test : IO Unit := do
  let tmpFile := "4573.tmp"
  let baseLines := #["foo", "bar", "foobar"]
  let content := baseLines[0] ++ "\r\n" ++ baseLines[1] ++ "\n" ++ baseLines[2]
  IO.FS.writeFile tmpFile content
  let readLines ← IO.FS.lines tmpFile
  IO.println <| baseLines == readLines
  IO.FS.removeFile tmpFile

/-- info: true -/
#guard_msgs in
#eval test
