/-!
# Temporary Files

These tests check that temporary files and directories can be created and used.
-/

/--
Tests temporary file creation.
-/
def test : IO Unit := do
  let (handle, path) ← IO.FS.createTempFile
  try
    let toWrite := "Hello World"
    handle.putStr toWrite
    handle.flush
    let handle2 ← IO.FS.Handle.mk path .read
    let content ← handle2.getLine
    assert! (content == toWrite)
  finally
    IO.FS.removeFile path

#eval test

/--
Tests temporary file helper.
-/
def testWithFile : IO Unit := do
  let pathRef ← IO.mkRef none
  IO.FS.withTempFile fun handle path => do
    pathRef.set (some path)
    assert! (← path.pathExists)
    let toWrite := "Hello World"
    handle.putStr toWrite
    handle.flush
    let handle2 ← IO.FS.Handle.mk path .read
    let content ← handle2.getLine
    assert! (content == toWrite)
  match (← pathRef.get) with
  | none => assert! false
  | some p => assert! (! (← p.pathExists))

#eval testWithFile

/--
Tests temporary directory creation and ensures that files can be created in it.
-/
def testDir : IO Unit := do
  let path ← IO.FS.createTempDir
  try
    assert! (← path.isDir)

    let fileList ← path.readDir
    assert! (fileList.isEmpty)

    let toWrite := "Hello World"
    for i in [0:3] do
      IO.FS.withFile (path / s!"{i}.txt") .write fun h => do
        h.putStr toWrite
        h.putStr (toString i)
    for i in [0:3] do
      IO.FS.withFile (path / s!"{i}.txt") .read fun h => do
        let content ← h.getLine
        assert! (content == toWrite ++ toString i)

    let fileList := ((← path.readDir).map (·.fileName)).qsortOrd
    assert! (fileList == #["0.txt",  "1.txt", "2.txt"])
  finally
    IO.FS.removeDirAll path

#eval testDir

/--
Tests temporary directory helper.
-/
def testWithDir : IO Unit := do
  let pathRef ← IO.mkRef none
  IO.FS.withTempDir fun path => do
    pathRef.set (some path)
    assert! (← path.isDir)

    let fileList ← path.readDir
    assert! (fileList.isEmpty)

    let toWrite := "Hello World"
    for i in [0:3] do
      IO.FS.withFile (path / s!"{i}.txt") .write fun h => do
        h.putStr toWrite
        h.putStr (toString i)
    for i in [0:3] do
      IO.FS.withFile (path / s!"{i}.txt") .read fun h => do
        let content ← h.getLine
        assert! (content == toWrite ++ toString i)

    let fileList := ((← path.readDir).map (·.fileName)).qsortOrd
    assert! (fileList == #["0.txt",  "1.txt", "2.txt"])
  match (← pathRef.get) with
  | none => assert! false
  | some p => assert! (! (← p.pathExists))

#eval testWithDir
