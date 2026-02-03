/-!
# File Seeking and Position Tests

These are tests for
  - `IO.FS.Handle.seek`
  - `IO.FS.Handle.tell`

These provide random access to file contents via the POSIX `fseek` and
`ftell` functions. We assume that the underlying POSIX implementation
is correct.
-/

/--
Run `action` on a temporary file containing the text `"Seek Test"`.

This function:
* creates a temporary directory
* writes `"Seek Test"` to a temporary file within the directory
* re-opens the file in read mode and passes its handle to `action`

The temporary directory and file are cleaned up automatically when
`action` finishes.
-/
private def withSeekTestFile (action : IO.FS.Handle → IO α) : IO α :=
  IO.FS.withTempDir fun tmpDir => do
    -- Create the file in write mode
    let fileName := tmpDir / "seek_test_file.txt"
    let contents := "Seek Test"
    IO.FS.withFile fileName .write fun h => h.putStr contents

    -- Open the file in read mode to run the action
    IO.FS.withFile fileName .read action

/--
Test that, on opening a file, the initial position is zero.
-/
def testTell0 : IO Unit :=
  withSeekTestFile fun h => do
    let pos0 ← h.tell
    assert! (pos0 == 0)

#eval testTell0

/--
Test seeking relative to the start location.
-/
def testSeekStart : IO Unit :=
  withSeekTestFile fun h => do
    -- Go to byte 5, which is 'T'
    h.seek .start 5
    let pos5 ← h.tell
    let byteArr ← h.read 1
    assert! (pos5 == 5)
    assert! (byteArr == "T".toUTF8)

#eval testSeekStart

/--
Test seeking relative to the end location.
-/
def testSeekEnd : IO Unit :=
  withSeekTestFile fun h => do
    -- Go to byte -4 from the end, which is 'T'
    h.seek .end (-4)
    let pos5 ← h.tell
    let byteArr ← h.read 1
    assert! (pos5 == 5)
    assert! (byteArr == "T".toUTF8)

#eval testSeekEnd

/--
Test seeking relative to the current location.

Both positive and negative offsets are tested.
-/
def testSeekCur : IO Unit :=
  withSeekTestFile fun h => do
    -- Go to byte 5 from the current location, which is 'T'
    h.seek .cur 5
    let pos5 ← h.tell
    let byteArr5 ← h.read 1
    assert! (pos5 == 5)
    assert! (byteArr5 == "T".toUTF8)

    -- After reading a byte, the position is advanced by 1.
    let pos6 ← h.tell
    assert! (pos6 == 6)

    -- Go to byte -3 from the current location, which is 'k'
    h.seek .cur (-3)
    let pos3 ← h.tell
    let byteArr3 ← h.read 1
    assert! (pos3 == 3)
    assert! (byteArr3 == "k".toUTF8)

#eval testSeekCur
