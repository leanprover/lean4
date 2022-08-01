/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Lake.Build.Job
import Lake.Config.Env

namespace Lake
open System

def createParentDirs (path : FilePath) : IO Unit := do
  if let some dir := path.parent then IO.FS.createDirAll dir

def proc (args : IO.Process.SpawnArgs) : BuildIO Unit := do
  let envStr := String.join <| args.env.toList.filterMap fun (k, v) =>
    if k == "PATH" then none else some s!"{k}={v.getD ""} " -- PATH too big
  let cmdStr := " ".intercalate (args.cmd :: args.args.toList)
  logVerbose <| "> " ++ envStr ++
    match args.cwd with
    | some cwd => s!"{cmdStr}    # in directory {cwd}"
    | none     => cmdStr
  let out ← IO.Process.output args
  let logOutputWith (log : String → BuildIO PUnit) := do
    unless out.stdout.isEmpty do
      log s!"stdout:\n{out.stdout}"
    unless out.stderr.isEmpty do
      log s!"stderr:\n{out.stderr}"
  if out.exitCode = 0 then
    logOutputWith logInfo
  else
    logOutputWith logError
    logError s!"external command {args.cmd} exited with status {out.exitCode}"
    failure

def compileLeanModule (name : String) (leanFile : FilePath)
(oleanFile? ileanFile? cFile? : Option FilePath)
(leanPath : SearchPath := []) (rootDir : FilePath := ".")
(dynlibs : Array FilePath := #[]) (dynlibPath : SearchPath := {})
(leanArgs : Array String := #[]) (lean : FilePath := "lean")
: BuildIO PUnit := do
  logAuxInfo s!"Building {name}"
  let mut args := leanArgs ++
    #[leanFile.toString, "-R", rootDir.toString]
  if let some oleanFile := oleanFile? then
    createParentDirs oleanFile
    args := args ++ #["-o", oleanFile.toString]
  if let some ileanFile := ileanFile? then
    createParentDirs ileanFile
    args := args ++ #["-i", ileanFile.toString]
  if let some cFile := cFile? then
    createParentDirs cFile
    args := args ++ #["-c", cFile.toString]
  for dynlib in dynlibs do
    args := args.push s!"--load-dynlib={dynlib}"
  proc {
    args
    cmd := lean.toString
    env := #[
      ("LEAN_PATH", leanPath.toString),
      (sharedLibPathEnvVar, (← getSearchPath sharedLibPathEnvVar) ++ dynlibPath |>.toString)
    ]
  }

def compileO (name : String) (oFile srcFile : FilePath)
(moreArgs : Array String := #[]) (compiler : FilePath := "cc") : BuildIO Unit := do
  logAuxInfo s!"Compiling {name}"
  createParentDirs oFile
  proc {
    cmd := compiler.toString
    args := #["-c", "-o", oFile.toString, srcFile.toString] ++ moreArgs
  }

def compileStaticLib (name : String) (libFile : FilePath)
(oFiles : Array FilePath) (ar : FilePath := "ar") : BuildIO Unit := do
  logAuxInfo s!"Linking {name}"
  createParentDirs libFile
  proc {
    cmd := ar.toString
    args := #["rcs", libFile.toString] ++ oFiles.map toString
  }

def compileSharedLib (name : String) (libFile : FilePath)
(linkArgs : Array String) (linker : FilePath := "cc") : BuildIO Unit := do
  logAuxInfo s!"Linking {name}"
  createParentDirs libFile
  proc {
    cmd := linker.toString
    args := #["-shared", "-o", libFile.toString] ++ linkArgs
  }

def compileExe (name : String) (binFile : FilePath) (linkFiles : Array FilePath)
(linkArgs : Array String := #[]) (linker : FilePath := "cc") : BuildIO Unit := do
  logAuxInfo s!"Linking {name}"
  createParentDirs binFile
  proc {
    cmd := linker.toString
    args := #["-o", binFile.toString] ++ linkFiles.map toString ++ linkArgs
  }

/-- Download a file using `curl`, clobbering any existing file. -/
def download (name : String) (url : String) (file : FilePath) : BuildIO PUnit := do
  logAuxInfo s!"Downloading {name}"
  if (← file.pathExists) then
    IO.FS.removeFile file
  else
    createParentDirs file
  let args :=
    if (← getIsVerbose) then #[] else #["-s"]
  proc {
    cmd := "curl"
    args := args ++ #["-f", "-o", file.toString, "-L", url]
  }

/-- Unpack an archive `file` using `tar` into the directory `dir`. -/
def untar (name : String) (file : FilePath) (dir : FilePath) (gzip := true) : BuildIO PUnit := do
  logAuxInfo s!"Unpacking {name}"
  let mut opts := "-x"
  if (← getIsVerbose) then
    opts := opts.push 'v'
  if gzip then
    opts := opts.push 'z'
  proc {
    cmd := "tar",
    args := #[opts, "-f", file.toString, "-C", dir.toString]
  }

/-- Pack a directory `dir` using `tar` into the archive `file`. -/
def tar (name : String) (dir : FilePath) (file : FilePath)
(gzip := true) (excludePaths : Array FilePath := #[]) : BuildIO PUnit := do
  logAuxInfo s!"Packing {name}"
  createParentDirs file
  let mut args := #["-c"]
  if gzip then
    args := args.push "-z"
  if (← getIsVerbose) then
    args := args.push "-v"
  for path in excludePaths do
    args := args.push s!"--exclude={path}"
  proc {
    cmd := "tar"
    args := args ++ #["-f", file.toString, "-C", dir.toString, "."]
  }
