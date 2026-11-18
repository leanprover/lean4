/-!
Tests that the `IO.FS.realPath` function on windows resolves links.
-/

def realPathTest : IO Unit := do
  unless System.Platform.isWindows do
    IO.println "This test only does something on Windows."
    return
  let dir ← IO.currentDir
  let tmpDir := dir / "tmp_realpath_test_dir"
  let tmpJunct := dir / "tmp_realpath_test_junction"
  IO.FS.createDir (dir / tmpDir)
  discard <| IO.Process.run
    { cmd := "cmd.exe", args := #["/c", "mklink", "/j", tmpJunct.toString, tmpDir.toString] }
  let realPath1 ← IO.FS.realPath tmpDir
  let realPath2 ← IO.FS.realPath tmpJunct
  IO.FS.removeDir tmpJunct
  IO.FS.removeDir tmpDir
  IO.println s!"{realPath1} vs {realPath2}"
  if realPath1 != realPath2 then
    throw (.userError ("mismatch " ++ realPath1.toString ++ " with " ++ realPath2.toString))

#eval realPathTest
