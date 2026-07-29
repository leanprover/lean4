import Std.FS
import Std.IO
import Std.Path.Notation

/-!
Tests for `Std.FS.File`: the handle-based operations, the path-keyed helpers that live alongside it,
and the `Std.IO` byte-stream instances it provides.
-/

open Std Std.FS

namespace StdFSFile

private def assertFails (action : IO α) : IO Unit := do
  let failed ← try
    discard action
    pure false
  catch _ =>
    pure true
  assert! failed

/-- Runs `f` with a fresh, empty directory that is removed afterwards. -/
private def withRoot (f : Path → IO α) : IO α :=
  IO.FS.withTempDir fun root => do f (← Path.fromString root.toString)

private def testWholeFile (root : Path) : IO Unit := do
  let file := root / path("notes.txt")
  writeFile file "hello\nworld\n"
  assert! (← readFile file) == "hello\nworld\n"
  assert! (← (← lines file).toArray) == #["hello", "world"]

  appendFile file "again\n"
  assert! (← readFile file) == "hello\nworld\nagain\n"

  let binary := root / path("data.bin")
  let bytes := ByteArray.mk #[0, 1, 2, 250, 255]
  writeBinFile binary bytes
  assert! (← readBinFile binary) == bytes
  appendBinFile binary (ByteArray.mk #[7])
  assert! (← readBinFile binary) == bytes ++ ByteArray.mk #[7]

  -- `writeFile` truncates, so the shorter contents fully replace the longer ones.
  writeFile file "hi"
  assert! (← readFile file) == "hi"

  -- A file whose bytes are not valid UTF-8 reads back as bytes but not as text.
  writeBinFile binary (ByteArray.mk #[0xff, 0xfe])
  assertFails (readFile binary)

  removeFile file
  removeFile binary
  assert! !(← pathExists file)

private def testLines (root : Path) : IO Unit := do
  let file := root / path("lines.txt")

  -- `\r\n` and `\n` both terminate a line, and neither terminator is part of it.
  writeFile file "one\r\ntwo\r\nthree"
  assert! (← (← lines file).toArray) == #["one", "two", "three"]
  -- A trailing terminator does not produce an empty final line, but interior blanks are kept.
  writeFile file "\n\na\n"
  assert! (← (← lines file).toArray) == #["", "", "a"]
  writeFile file ""
  assert! (← (← lines file).toArray) == #[]

  -- A line longer than the read chunk size spans several reads.
  let long := String.ofList (List.replicate 200000 'x')
  writeFile file (long ++ "\nshort\n")
  assert! (← (← lines file).toArray) == #[long, "short"]

  -- The iterator is lazy: stopping early does not read the rest of the file.
  writeFile file "a\nb\nc\n"
  File.withFile file .readOnly fun handle => do
    let mut seen := #[]
    for line in ← handle.lines do
      seen := seen.push line
      if seen.size == 2 then break
    assert! seen == #["a", "b"]

  -- Decoding failures surface when the offending line is reached.
  writeBinFile file (ByteArray.mk #[0xff, 0xfe, 0x0a])
  assertFails ((← lines file).toArray)

  removeFile file

private def testHandleIO (root : Path) : IO Unit := do
  let file := root / path("handle.txt")

  File.withFile file .writeCreate fun handle => do
    handle.putStr "abc"
    handle.putStrLn "def"
  assert! (← readFile file) == "abcdef\n"

  -- Positioned writes leave the cursor alone, so the sequential write lands at the start.
  File.withFile file .readWrite fun handle => do
    handle.writeAt 0 "XYZ".toUTF8
    handle.write "0".toUTF8
  assert! (← readFile file) == "0YZdef\n"

  File.withFile file .readOnly fun handle => do
    assert! (← handle.readAt 0 3 .empty) == "0YZ".toUTF8
    -- `readAt` does not move the cursor, so the sequential read still starts from the beginning.
    assert! (← handle.read 3 .empty) == "0YZ".toUTF8
    assert! (← handle.read 3 .empty) == "def".toUTF8
    -- Reading past the end yields no bytes rather than failing.
    assert! (← handle.readAt 100 8 .empty) == .empty

  File.withFile file .readOnly fun handle => do
    assert! (← handle.readToEndAt 0) == "0YZdef\n".toUTF8
    assert! (← handle.readStringToEndAt 3) == "def\n"
    -- Starting at or past the end yields nothing.
    assert! (← handle.readToEndAt 7) == .empty
    assert! (← handle.readToEndAt 100) == .empty
    -- The positional reads above left the cursor alone, so this still sees the whole file.
    assert! (← handle.readStringToEnd) == "0YZdef\n"
    -- ... and now the cursor sits at the end.
    assert! (← handle.readToEnd) == .empty

  -- Reads spanning many chunks, to exercise the accumulation loop rather than a single read.
  let big := root / path("big.bin")
  let chunk := ByteArray.mk (Array.replicate 1024 0x61)
  File.withFile big .writeCreate fun handle =>
    for _ in [0:400] do handle.write chunk
  File.withFile big .readOnly fun handle => do
    let bytes ← handle.readToEnd
    assert! bytes.size == 400 * 1024
    assert! bytes.data.all (· == 0x61)
    assert! (← handle.readToEndAt (400 * 1024 - 3)).size == 3
  assert! (← readBinFile big).size == 400 * 1024
  removeFile big

  -- Invalid UTF-8 fails to decode as text but still reads back as bytes.
  let raw := root / path("raw.bin")
  writeBinFile raw (ByteArray.mk #[0xff, 0xfe])
  File.withFile raw .readOnly fun handle => do
    assert! (← handle.readToEnd) == ByteArray.mk #[0xff, 0xfe]
  assertFails (File.withFile raw .readOnly (·.readStringToEnd))
  removeFile raw

  File.withFile file .readWrite fun handle => do
    handle.setLength 3
    assert! (← handle.metadata).byteSize == 3
    -- Extending fills the gap with zeros.
    handle.setLength 5
    assert! (← handle.readAt 0 8 .empty) == "0YZ".toUTF8 ++ ByteArray.mk #[0, 0]
    handle.syncData
    handle.syncAll

  -- `withFile` closes on the way out, and a closed file rejects further operations.
  let closed ← File.open file
  closed.close
  assertFails closed.metadata

  -- Opening a directory read-only succeeds at the OS level, so `File.open` has to reject it.
  assertFails (File.open root)

  -- A mode that does not create leaves a missing path untouched.
  let missing := root / path("missing")
  assertFails (File.open missing)
  assertFails (File.open missing .readWrite)
  assert! !(← pathExists missing)
  -- `create` brings it into existence, with the permissions it was given.
  let perm : FileRight := { user := { read := true, write := true } }
  (← File.create missing perm).close
  assert! ← pathExists missing
  assert! (← getPermissions missing) == perm
  removeFile missing

  removeFile file

private def testLocking (root : Path) : IO Unit := do
  let file := root / path("locked.txt")
  writeFile file "x"
  File.withFile file .readWrite fun handle => do
    handle.lock (exclusive := true)
    handle.unlock
    -- Unlocking twice is fine: releasing a lock nobody holds succeeds.
    handle.unlock
    assert! ← handle.tryLock (exclusive := false)
    handle.unlock
    handle.withLock (exclusive := true) do
      handle.putStr "y"
  removeFile file

private def testMetadata (root : Path) : IO Unit := do
  let file := root / path("meta.txt")
  writeFile file "12345"

  let md ← metadata file
  assert! md.byteSize == 5
  assert! md.type == .file
  assert! ← isFile file
  assert! ← pathExists file
  assert! !(← isSymlink file)
  assert! !(← isFile (root / path("missing")))
  assert! !(← pathExists (root / path("missing")))
  assert! (← fileSystemStats file).blockSize > 0

  -- The type predicates agree with the `type` field they read.
  assert! md.isFile
  assert! !md.isDir
  assert! !md.isSymlink
  assert! (← metadata root).isDir
  assert! FileType.file.isFile
  assert! FileType.dir.isDir
  assert! FileType.symlink.isSymlink
  assert! !FileType.unknown.isFile

  -- A birth time is either reported or absent. Platforms and filesystems that do not record one
  -- report an all-zero timespec, which must not surface as a timestamp at the epoch.
  match md.creationTime with
  | none => pure ()
  | some created => assert! created != Time.Timestamp.ofNanosecondsSinceUnixEpoch 0

  -- `FileType.ofMode` classifies the entry kind in C, so check a kind other than regular
  -- files, directories and symlinks. Windows has no character-device path to point at.
  assert! (← metadata root).type == .dir
  unless System.Platform.isWindows do
    assert! (← metadata (← Path.fromString "/dev/null")).type == .charDevice

  -- Both spellings of the same open file agree, and `sameFile` recognizes them as one file.
  let viaHandle ← File.withFile file .readOnly (·.metadata)
  assert! Metadata.sameFile md viaHandle

  let perms : FileRight := { user := { read := true, write := true }, group := { read := true } }
  setPermissions file perms
  assert! (← getPermissions file) == perms
  File.withFile file .readOnly fun handle => do
    assert! (← handle.getPermissions) == perms
    handle.setPermissions .default
  assert! (← getPermissions file) == FileRight.default

  let epoch := Time.Timestamp.ofNanosecondsSinceUnixEpoch 1000000000
  setTimes file epoch epoch
  assert! (← metadata file).modified == epoch
  File.withFile file .readWrite fun handle => handle.setTimes epoch epoch

  removeFile file

private def testStructural (root : Path) : IO Unit := do
  let src := root / path("src.txt")
  let dst := root / path("dst.txt")
  writeFile src "content"

  copyFile src dst
  assert! (← readFile dst) == "content"
  -- A copy is a distinct file, unlike a hard link.
  assert! !(Metadata.sameFile (← metadata src) (← metadata dst))

  let hard := root / path("hard.txt")
  hardLink src hard
  assert! Metadata.sameFile (← metadata src) (← metadata hard)

  let moved := root / path("moved.txt")
  rename dst moved
  assert! ← pathExists moved
  assert! !(← pathExists dst)

  truncate moved 3
  assert! (← readFile moved) == "con"

  removeFile src
  removeFile hard
  removeFile moved

private def testSymlinks (root : Path) : IO Unit := do
  -- Symlink creation needs a privilege on Windows that the test environment may not have.
  if System.Platform.isWindows then
    return

  let target := root / path("target.txt")
  let link := root / path("link.txt")
  writeFile target "linked"
  createSymlink (← Path.fromString "target.txt") link

  assert! ← isSymlink link
  -- `readSymlink` reports the stored target verbatim, without resolving it.
  assert! (← readSymlink link) == (← Path.fromString "target.txt")
  -- `metadata` follows the link while `symlinkMetadata` describes the link itself.
  assert! (← metadata link).type == .file
  assert! (← symlinkMetadata link).type == .symlink
  assert! (← readFile link) == "linked"

  let epoch := Time.Timestamp.ofNanosecondsSinceUnixEpoch 1000000000
  setSymlinkTimes link epoch epoch

  removeFile link
  removeFile target

private def testTempFiles : IO Unit := do
  let (file, path) ← createTempFile
  file.putStr "scratch"
  file.close
  assert! (← readFile path) == "scratch"
  removeFile path

  let leaked ← withTempFile fun file path => do
    file.putStr "temporary"
    assert! ← pathExists path
    pure path
  -- `withTempFile` deletes the file it created.
  assert! !(← pathExists leaked)

  let root ← tempDir
  let inRoot ← withTempFileIn root fun _ path => pure path
  assert! !(← pathExists inRoot)

private def testHandlePath (root : Path) : IO Unit := do
  let file := root / path("named.txt")
  writeFile file "named"

  -- The handle reports the path it was opened at, verbatim rather than resolved.
  File.withFile file .readOnly fun handle => do
    assert! handle.path == file
  let handle ← File.open file
  assert! handle.path == file
  handle.close

  -- The path is kept as given rather than resolved, so two spellings of one file report back the
  -- spelling each was opened with.
  let spelled := root / path("./named.txt")
  File.withFile spelled .readOnly fun handle => do
    assert! handle.path == spelled
    assert! handle.path != file

  -- A path is recorded once, so it still names the original after the file moves away.
  let moved := root / path("moved-away.txt")
  let handle ← File.open file
  rename file moved
  assert! handle.path == file
  handle.close
  removeFile moved

  -- Temporary files report the path that was created for them.
  let (temp, tempPath) ← createTempFile
  assert! temp.path == tempPath
  temp.close
  removeFile tempPath

private def testAccess (root : Path) : IO Unit := do
  let file := root / path("access.txt")
  writeFile file "readable"

  assert! ← access file
  assert! ← access root
  assert! !(← access (root / path("missing")))

  assert! ← access file { read := true }
  assert! !(← access (root / path("missing")) { read := true })

  assert! ← access root { read := true, execution := true }
  assert! !(← access (file / path("under-a-file")) { read := true })

  removeFile file

private def testSendFile (root : Path) : IO Unit := do
  let src := root / path("send-src.bin")
  let dst := root / path("send-dst.bin")
  writeFile src "abcdef"
  writeFile dst ""
  File.withFile src .readOnly fun input =>
    File.withFile dst .readWrite fun output => do
      assert! (← File.sendFile input output 1 3) == 3
  assert! (← readFile dst) == "bcd"
  removeFile src
  removeFile dst

/--
`File` implements the `Std.IO` byte-stream classes, so code written against them works on a file
without naming `File` itself.
-/
private def drain [Monad m] [Std.IO.Read m α] (source : α) : m ByteArray := do
  let mut acc := ByteArray.empty
  repeat
    let chunk ← Std.IO.Read.read source 4 .empty
    if chunk.isEmpty then break
    acc := acc ++ chunk
  return acc

private def testIOClasses (root : Path) : IO Unit := do
  let file := root / path("classes.txt")
  writeFile file ""

  File.withFile file .readWrite fun handle => do
    Std.IO.Write.write handle "streamed".toUTF8
    assert! (← Std.IO.Size.size handle) == 8
    Std.IO.WriteAt.writeAt handle 0 "S".toUTF8
    assert! (← Std.IO.ReadAt.readAt handle 0 8 .empty) == "Streamed".toUTF8

  File.withFile file .readOnly fun handle => do
    assert! (← drain handle) == "Streamed".toUTF8

  -- A `Cursor` supplies its own position on top of the positional operations, so seeking moves the
  -- cursor rather than the descriptor's own offset.
  File.withFile file .readOnly fun handle => do
    let cursor : Std.IO.Cursor File ← Std.IO.Cursor.new handle
    assert! (← Std.IO.Read.read cursor 6 .empty) == "Stream".toUTF8
    assert! (← Std.IO.Seek.position cursor) == 6
    assert! (← Std.IO.Seek.seek cursor (.start 2)) == 2
    assert! (← Std.IO.Read.read cursor 4 .empty) == "ream".toUTF8
    -- `.end` needs the file's size, which `File` reports through `Std.IO.Size`.
    assert! (← Std.IO.Seek.seek cursor (.end (-3))) == 5
    assert! (← Std.IO.Read.read cursor 8 .empty) == "med".toUTF8
    Std.IO.Seek.rewind cursor
    assert! (← Std.IO.Seek.position cursor) == 0
    -- Seeking before the start fails rather than wrapping around.
    assertFails (Std.IO.Seek.seek cursor (.current (-1)))

  removeFile file

def test : IO Unit := do
  withRoot testWholeFile
  withRoot testLines
  withRoot testHandleIO
  withRoot testLocking
  withRoot testMetadata
  withRoot testStructural
  withRoot testSymlinks
  testTempFiles
  withRoot testHandlePath
  withRoot testAccess
  withRoot testSendFile
  withRoot testIOClasses

end StdFSFile

#eval StdFSFile.test
