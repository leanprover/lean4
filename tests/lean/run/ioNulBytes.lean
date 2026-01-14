/-!
# Test that IO functions error when inputs contain NUL bytes
-/

def checkError (x : IO α) : IO Unit := do
  try
    discard x
    throw (.userError "error expected")
  catch e =>
    unless e matches .invalidArgument .. do
      throw e

def badPath : System.FilePath := "Path with\x00NUL"

#eval checkError <| IO.setAccessRights badPath {}
#eval checkError <| IO.FS.Handle.mk badPath .read
#eval checkError <| IO.FS.realPath badPath
#eval checkError <| badPath.readDir
#eval checkError <| badPath.metadata
#eval checkError <| badPath.symlinkMetadata
#eval checkError <| IO.FS.createDir badPath
#eval checkError <| IO.FS.createDirAll badPath
#eval checkError <| IO.FS.removeDir badPath
#eval checkError <| IO.FS.removeDirAll badPath
#eval checkError <| IO.FS.removeFile badPath
#eval checkError <| IO.FS.rename badPath badPath

/-- info: none -/
#guard_msgs in
#eval IO.getEnv "Path with\x00NUL"
