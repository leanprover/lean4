def test : IO Unit := do
  let (handle, path) ← IO.FS.createTempFile
  let toWrite := "Hello World"
  handle.putStr toWrite
  let handle2 ← IO.FS.Handle.mk path .read
  let content ← handle2.getLine
  assert! (content == toWrite)
  IO.FS.removeFile path

#eval test
