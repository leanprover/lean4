/-!
Some kinds of `IO.Error` carry no file name, so the runtime drops the name a file operation passes
when the system reports an error of such a kind. Builds with assertions used to abort there. Two
ways to get there: removing a non-empty directory (`ENOTEMPTY`), and opening a running executable
for writing (`ETXTBSY` on Linux; other platforms may let that open succeed).
-/

def main : IO Unit := do
  IO.FS.createDirAll "_tmp_io_error_without_file_name/sub"
  try IO.FS.removeDir "_tmp_io_error_without_file_name"
  catch _ => pure ()
  IO.FS.removeDirAll "_tmp_io_error_without_file_name"
  try discard <| IO.FS.Handle.mk (← IO.appPath) .readWrite
  catch _ => pure ()
  IO.println "done"
