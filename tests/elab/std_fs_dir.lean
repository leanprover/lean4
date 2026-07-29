import Std.FS
import Std.IO
import Std.Path.Notation

/-!
Tests for `Std.FS.Dir`: the open directory stream, the `DirEntry` values it produces, and the
path-keyed operations that create, list, copy, and remove directories.
-/

open Std Std.FS

namespace StdFSDir

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

/-- The entry names of `entries`, sorted, so that comparisons do not depend on filesystem order. -/
private def names (entries : Array DirEntry) : Array String :=
  entries.map (·.fileName.value) |>.qsort (· < ·)

private def findEntry (entries : Array DirEntry) (name : String) : IO DirEntry := do
  let some entry := entries.find? (·.fileName.value == name)
    | throw <| IO.userError s!"no entry named {name}"
  return entry

/-- Builds `a/`, `a/b/`, `a/b/deep.txt`, and `top.txt` under `root`. -/
private def buildTree (root : Path) : IO Unit := do
  createDirAll (root / path("a") / path("b"))
  writeFile (root / path("top.txt")) "top"
  writeFile (root / path("a") / path("b") / path("deep.txt")) "deep"

private def testCreateRemove (root : Path) : IO Unit := do
  let one := root / path("one")
  assert! !(← isDir one)
  createDir one
  assert! ← isDir one
  assert! (← metadata one).type == .dir
  -- A path that exists as a file is not a directory, and creating over it fails.
  writeFile (root / path("file.txt")) "x"
  assert! !(← isDir (root / path("file.txt")))
  assertFails (createDir (root / path("file.txt")))
  -- `createDir` needs the parent to exist; `createDirAll` creates the whole chain.
  let deep := root / path("x") / path("y") / path("z")
  assertFails (createDir deep)
  createDirAll deep
  assert! ← isDir deep
  -- `createDirAll` is a no-op on an existing directory, while `createDir` fails.
  createDirAll deep
  assertFails (createDir deep)

  -- `removeDir` only removes empty directories.
  assertFails (removeDir (root / path("x")))
  removeDir deep
  assert! !(← isDir deep)
  removeDirAll (root / path("x"))
  assert! !(← isDir (root / path("x")))
  -- `removeDirAll` removes the contents along with the directory.
  writeFile (one / path("inner.txt")) "inner"
  createDir (one / path("nested"))
  writeFile (one / path("nested") / path("leaf.txt")) "leaf"
  removeDirAll one
  assert! !(← pathExists one)

  -- Removing something that is not there fails unless the errors are being ignored.
  assertFails (removeDirAll (root / path("gone")))
  removeDirAll (root / path("gone")) (ignoreErrors := true)

  removeFile (root / path("file.txt"))

private def testReadDir (root : Path) : IO Unit := do
  assert! (← readDir root).isEmpty
  buildTree root

  let entries ← readDir root
  assert! names entries == #["a", "top.txt"]
  -- `.` and `..` are never reported.
  assert! !(names entries).contains "."

  -- Every entry names one file within the directory it was read from.
  for entry in entries do
    assert! entry.parent == root
    assert! entry.path == root / entry.fileName

  let sorted ← readDirSorted root
  assert! sorted.map (·.fileName.value) == #["a", "top.txt"]

  -- Entry kinds come from the directory read where the filesystem reports them, and agree with
  -- what a metadata query says either way.
  let dirEntry ← findEntry sorted "a"
  let fileEntry ← findEntry sorted "top.txt"
  assert! (← dirEntry.fileType) == .dir
  assert! (← dirEntry.isDir)
  assert! (← fileEntry.fileType) == .file
  assert! !(← fileEntry.isDir)
  assert! (← fileEntry.metadata).byteSize == 3

  assertFails (readDir (root / path("missing")))
  -- A regular file is not a directory stream.
  assertFails (readDir (root / path("top.txt")))

private def testDirHandle (root : Path) : IO Unit := do
  buildTree root

  Dir.withDir root fun dir => do
    assert! dir.path == root
    assert! (← dir.metadata).type == .dir
    -- Reading advances the stream, so draining afterwards only sees what is left.
    let first ← dir.next
    assert! first.isSome
    let rest ← dir.drain
    assert! rest.size == 1
    -- Once exhausted, the stream keeps reporting `none`.
    assert! (← dir.next).isNone
    assert! (← dir.drain).isEmpty

  -- The iterator pulls one entry per step and stops when the stream is exhausted.
  Dir.withDir root fun dir => do
    let mut seen := #[]
    for entry in dir.iter do
      seen := seen.push entry
    assert! names seen == #["a", "top.txt"]

  -- Stopping early leaves the rest of the stream unread.
  Dir.withDir root fun dir => do
    for _ in dir.iter do
      break
    assert! (← dir.drain).size == 1

  -- `withDir` closes on the way out, and a closed directory rejects further reads.
  let closed ← Dir.open root
  closed.close
  assertFails closed.next
  -- The `Std.IO.Close` instance is the same operation.
  let viaClass ← Dir.open root
  Std.IO.Close.close viaClass
  assertFails viaClass.next

  assertFails (Dir.open (root / path("missing")))
  assertFails (Dir.open (root / path("top.txt")))

private def testWalk (root : Path) : IO Unit := do
  buildTree root

  let all ← (← walk root).toArray
  assert! names all == #["a", "b", "deep.txt", "top.txt"]
  -- Each entry knows the directory it was found in, not just the root of the walk.
  let deep ← findEntry all "deep.txt"
  assert! deep.parent == root / path("a") / path("b")
  assert! (← readFile deep.path) == "deep"

  -- The walk is lazy: stopping early does not read the rest of the tree.
  let mut seen := #[]
  for entry in ← walk root do
    seen := seen.push entry.fileName.value
    break
  assert! seen.size == 1

  -- A root that cannot be read fails eagerly, even with `ignoreErrors`.
  assertFails (walk (root / path("missing")))
  assertFails (walk (root / path("missing")) (ignoreErrors := true))

  let matched ← (← glob root "**/*.txt").toArray
  assert! names matched == #["deep.txt", "top.txt"]
  assert! (← (← glob root "**/deep.*").toArray).size == 1
  assert! (← (← glob root "**/*.none").toArray).isEmpty
  -- An invalid pattern matches nothing rather than failing, as in `Path.matchGlob`.
  assert! (← (← glob root "**/[unterminated").toArray).isEmpty

  -- Like `walk`, the glob is lazy: stopping early does not read the rest of the tree.
  let mut globbed := #[]
  for entry in ← glob root "**/*.txt" do
    globbed := globbed.push entry.fileName.value
    break
  assert! globbed.size == 1

private def testWalkSymlinks (root : Path) : IO Unit := do
  -- Symlink creation needs a privilege on Windows that the test environment may not have.
  if System.Platform.isWindows then
    return

  buildTree root
  -- A link pointing back at the root would make a following traversal loop forever.
  createSymlink root (root / path("loop")) (dir := true)

  let all ← (← walk root).toArray
  assert! names all == #["a", "b", "deep.txt", "loop", "top.txt"]
  let loop ← findEntry all "loop"
  -- The link is reported as a link, not as the directory it points at.
  assert! (← loop.fileType) == .symlink
  assert! !(← loop.isDir)
  -- ... while its metadata follows the link.
  assert! (← loop.metadata).type == .dir

  removeFile (root / path("loop"))

private def testIgnoreErrors (root : Path) : IO Unit := do
  -- Making a directory unreadable needs POSIX permission bits, and root can read it regardless.
  if System.Platform.isWindows || (← metadata root).uid == some 0 then
    return

  let tree := root / path("tree")
  createDir tree
  buildTree tree
  let locked := tree / path("locked")
  createDir locked
  writeFile (locked / path("hidden.txt")) "hidden"
  setPermissions locked {}

  -- The unreadable subtree aborts the walk by default and is skipped when asked.
  assertFails ((← walk tree).toArray)
  let seen ← (← walk tree (ignoreErrors := true)).toArray
  assert! names seen == #["a", "b", "deep.txt", "locked", "top.txt"]

  -- The same holds for a removal that cannot descend into the subtree.
  assertFails (removeDirAll tree)
  removeDirAll tree (ignoreErrors := true)
  assert! ← pathExists locked

  setPermissions locked .defaultDir
  removeDirAll tree
  assert! !(← pathExists tree)

private def testCopyDir (root : Path) : IO Unit := do
  buildTree root
  let src := root / path("a")
  let dst := root / path("copied")

  copyDir src dst
  assert! ← isDir dst
  assert! (← readFile (dst / path("b") / path("deep.txt"))) == "deep"
  -- The copy is a distinct tree, not a link to the original.
  assert! !(Metadata.sameFile (← metadata (src / path("b") / path("deep.txt")))
                              (← metadata (dst / path("b") / path("deep.txt"))))

  -- The destination must not exist.
  assertFails (copyDir src dst)
  copyDir src dst (ignoreErrors := true)

  unless System.Platform.isWindows do
    -- Symlinks are recreated verbatim rather than followed.
    let linked := root / path("linked")
    createDir linked
    createSymlink (← Path.fromString "../top.txt") (linked / path("link.txt"))
    copyDir linked (root / path("linked-copy"))
    assert! ← isSymlink (root / path("linked-copy") / path("link.txt"))
    assert! (← readSymlink (root / path("linked-copy") / path("link.txt")))
              == (← Path.fromString "../top.txt")

private def testTempDirs : IO Unit := do
  let dir ← createTempDir
  assert! ← isDir dir
  writeFile (dir / path("scratch.txt")) "scratch"
  removeDirAll dir
  assert! !(← pathExists dir)

  let leaked ← withTempDir fun dir => do
    writeFile (dir / path("scratch.txt")) "scratch"
    assert! ← isDir dir
    pure dir
  -- `withTempDir` removes the directory it created, contents and all.
  assert! !(← pathExists leaked)

  let inRoot ← withTempDirIn (← tempDir) fun dir => do
    createDir (dir / path("nested"))
    pure dir
  assert! !(← pathExists inRoot)

  -- Two temporary directories never collide.
  let a ← createTempDir
  let b ← createTempDir
  assert! a != b
  removeDir a
  removeDir b

def test : IO Unit := do
  withRoot testCreateRemove
  withRoot testReadDir
  withRoot testDirHandle
  withRoot testWalk
  withRoot testWalkSymlinks
  withRoot testIgnoreErrors
  withRoot testCopyDir
  testTempDirs

end StdFSDir

#eval StdFSDir.test
