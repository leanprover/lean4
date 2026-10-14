module

import Lake.Util.IO

/-!
Regression tests for #14476: recursive deletion must unlink a root symlink without deleting its
target. Check both Lean and Lake, including child links, dangling links, files, and missing paths.
-/

open System

def checkAbsent (path : FilePath) : IO Unit := do
  let result ← path.symlinkMetadata.toBaseIO
  match result with
  | .error (.noFileOrDirectory ..) => pure ()
  | .error e => throw e
  | .ok _ => throw <| IO.userError s!"path still exists: {path}"

def checkRemoveDirAll (remove : FilePath → IO Unit) (ignoreMissing : Bool) : IO Unit :=
  IO.FS.withTempDir fun root => do
    let target := root / "target"
    let sentinel := target / "sub" / "sentinel"
    IO.FS.createDirAll (target / "sub")
    IO.FS.writeFile sentinel "preserve this file"
    let dir := root / "dir"
    IO.FS.createDirAll (dir / "sub")
    IO.FS.writeFile (dir / "sub" / "file") "delete this file"
    unless System.Platform.isWindows do
      let _ ← IO.Process.run { cmd := "ln", args := #["-s", "../target", (dir / "link").toString] }
      let _ ← IO.Process.run { cmd := "ln", args := #["-s", "../missing", (dir / "dangling").toString] }
    remove dir
    checkAbsent dir
    assert! (← IO.FS.readFile sentinel) == "preserve this file"

    let empty := root / "empty"
    IO.FS.createDir empty
    remove empty
    checkAbsent empty

    let missing := root / "missing"
    let result ← (remove missing).toBaseIO
    match result with
    | .ok () => assert! ignoreMissing
    | .error (.noFileOrDirectory ..) => assert! !ignoreMissing
    | .error e => throw e

    let file := root / "file"
    IO.FS.writeFile file "keep this ordinary file"
    let result ← (remove file).toBaseIO
    assert! result matches .error _
    assert! (← IO.FS.readFile file) == "keep this ordinary file"

    -- symlinkMetadata currently follows links on Windows.
    unless System.Platform.isWindows do
      for dest in [target.toString, "target", "file", "missing"] do
        let link := root / "link"
        let _ ← IO.Process.run { cmd := "ln", args := #["-s", dest, link.toString] }
        assert! (← link.symlinkMetadata).type == .symlink
        remove link
        checkAbsent link
        assert! (← IO.FS.readFile sentinel) == "preserve this file"
        assert! (← IO.FS.readFile file) == "keep this ordinary file"
        checkAbsent missing

#eval checkRemoveDirAll IO.FS.removeDirAll false
#eval checkRemoveDirAll Lake.removeDirAllIfExists true
