def realPathTest : IO Unit := do
  unless System.Platform.isWindows do
    return
  let dir ← IO.currentDir
  let tmpDir := dir / "tmp_realpath_test_dir"
  let tmpJunct := dir / "tmp_realpath_test_junction"
  IO.FS.createDir (dir / tmpDir)
  let cmd := "cmd.exe\" /c mklink /j \"" ++ tmpJunct.toString ++ "\" \"" ++ tmpDir.toString
  discard <| IO.Process.run { cmd }
  let realPath1 ← IO.FS.realPath tmpDir
  let realPath2 ← IO.FS.realPath tmpJunct
  let cmd := "cmd.exe\" /c rmdir \"" ++ tmpJunct.toString
  discard <| IO.Process.run { cmd }
  let cmd := "cmd.exe\" /c rmdir \"" ++ tmpDir.toString
  discard <| IO.Process.run { cmd }
  if realPath1 != realPath2 then
    throw (.userError ("mismatch " ++ realPath1.toString ++ " with " ++ realPath2.toString))

#eval realPathTest
