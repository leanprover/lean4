import Std.Internal.FS

/-!
Exercises the raw filesystem primitives that back `Std.FS.File` and `Std.FS.Dir`.
-/

namespace UVFS

open Std.Internal.FS

private def assertFails (action : IO α) : IO Unit := do
  let failed ← try
    discard action
    pure false
  catch _ =>
    pure true
  assert! failed

private def testDescriptorOps (dirString : String) : IO Unit := do
  let (fd, path) ← createTempFile (dirString ++ "/item-XXXXXX")
  let data := "abcdef".toUTF8
  assert! (← write fd data 0) == data.size.toUSize
  syncAll fd
  syncData fd
  let fileStat ← fileMetadata fd
  assert! fileStat.size == 6
  setFilePermissions fd 0o600
  unless System.Platform.isWindows do
    setFileOwner fd fileStat.uid.toUInt32 fileStat.gid.toUInt32
  setFileTimes fd 1.0 2.0
  assert! (← read fd 6 0 ByteArray.empty) == data
  -- `-1` reads at the descriptor's own cursor, which the positioned read above left untouched.
  assert! (← read fd 6 (-1) ByteArray.empty) == data
  setLength fd 3
  assert! (← fileMetadata fd).size == 3
  lock fd true
  unlock fd
  assert! ← tryLock fd false
  unlock fd
  close fd
  -- Operating on a closed descriptor fails rather than reusing a stale fd.
  assertFails (fileMetadata fd)

  let readFd ← openFile path 0 0
  assert! (← read readFd 8 0 ByteArray.empty) == "abc".toUTF8
  close readFd
  removeFile path

private def testSendfile (dirString : String) : IO Unit := do
  let (srcFd, srcPath) ← createTempFile (dirString ++ "/send-XXXXXX")
  discard <| write srcFd "abc".toUTF8 0
  close srcFd
  let src ← openFile srcPath 0 0
  let (dstFd, dstPath) ← createTempFile (dirString ++ "/sent-XXXXXX")
  assert! (← sendFile dstFd src 0 3) == 3
  close src
  close dstFd
  assert! (← IO.FS.readBinFile dstPath) == "abc".toUTF8
  removeFile srcPath
  removeFile dstPath

private def testPathOps (dirString : String) : IO Unit := do
  let (fd, path) ← createTempFile (dirString ++ "/item-XXXXXX")
  discard <| write fd "abc".toUTF8 0
  close fd

  let copy := dirString ++ "/copy"
  let hardLinkPath := dirString ++ "/hard-link"
  let renamed := dirString ++ "/renamed"
  copyFile path copy 0
  hardLink copy hardLinkPath
  rename hardLinkPath renamed
  let renamedStat ← metadata renamed
  assert! renamedStat.size == 3
  assert! (← symlinkMetadata renamed).size == 3
  assert! (← filesystemStats renamed).blockSize > 0
  setPermissions renamed 0o600
  setTimes renamed 3.0 4.0

  unless System.Platform.isWindows do
    setOwner renamed renamedStat.uid.toUInt32 renamedStat.gid.toUInt32
    let symlinkPath := dirString ++ "/symlink"
    createSymlink "renamed" symlinkPath 0
    setSymlinkOwner symlinkPath renamedStat.uid.toUInt32 renamedStat.gid.toUInt32
    setSymlinkTimes symlinkPath 3.0 4.0
    assert! (← readSymlink symlinkPath) == "renamed"
    removeFile symlinkPath

  removeFile path
  removeFile copy
  removeFile renamed
  assert! !(← access renamed 0)
  assertFails (metadata renamed)
  assertFails (metadata (dirString ++ "/bad\x00path"))
  assertFails (rename (dirString ++ "/bad\x00path") renamed)

private def testDirOps (dirString : String) : IO Unit := do
  -- `createTempDir` fills in the trailing `XXXXXX`, so the created path is not the template.
  let nested ← createTempDir (dirString ++ "/dir-XXXXXX")
  assert! nested != dirString ++ "/dir-XXXXXX"
  assert! ← access nested 0

  createDir (nested ++ "/inner") 0o755
  close (← openFile (nested ++ "/entry") (openFlags false true false false true false) 0o644)

  let dir ← openDir nested
  let mut names := #[]
  repeat
    let some ent ← readDirEntry dir | break
    names := names.push ent.name
  closeDir dir
  -- `.` and `..` are filtered out, leaving exactly the two entries created above.
  assert! names.qsort (· < ·) == #["entry", "inner"]
  -- Operating on a closed stream fails rather than reusing a stale handle.
  assertFails (readDirEntry dir)

  -- A directory has to be empty before it can be removed.
  assertFails (removeDir nested)
  removeFile (nested ++ "/entry")
  removeDir (nested ++ "/inner")
  removeDir nested
  assertFails (removeDir nested)
  assertFails (openDir nested)

def test : IO Unit :=
  IO.FS.withTempDir fun root => do
    let dirString := root.toString
    assert! ← access dirString 0
    testDescriptorOps dirString
    testSendfile dirString
    testPathOps dirString
    testDirOps dirString

end UVFS

#eval UVFS.test
