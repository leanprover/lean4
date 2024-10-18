/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone, Siddharth Bhat
-/
import Lake.Util.Proc
import Lake.Util.NativeLib
import Lake.Util.IO

/-! # Common Build Actions
Low level actions to build common Lean artifacts via the Lean toolchain.
-/

open System
open Lean hiding SearchPath

namespace Lake

def compileLeanModule
  (leanFile : FilePath)
  (oleanFile? ileanFile? cFile? bcFile?: Option FilePath)
  (leanPath : SearchPath := []) (rootDir : FilePath := ".")
  (dynlibs : Array FilePath := #[]) (dynlibPath : SearchPath := {})
  (leanArgs : Array String := #[]) (lean : FilePath := "lean")
: LogIO Unit := do
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
  if let some bcFile := bcFile? then
    createParentDirs bcFile
    args := args ++ #["-b", bcFile.toString]
  for dynlib in dynlibs do
    args := args.push s!"--load-dynlib={dynlib}"
  args := args.push "--json"
  withLogErrorPos do
  let out ← rawProc {
    args
    cmd := lean.toString
    env := #[
      ("LEAN_PATH", leanPath.toString),
      (sharedLibPathEnvVar, (← getSearchPath sharedLibPathEnvVar) ++ dynlibPath |>.toString)
    ]
  }
  unless out.stdout.isEmpty do
    let txt ← out.stdout.split (· == '\n') |>.foldlM (init := "") fun txt ln => do
      if let .ok (msg : SerialMessage) := Json.parse ln >>= fromJson? then
        unless txt.isEmpty do
          logInfo s!"stdout:\n{txt}"
        logSerialMessage msg
        return txt
      else if txt.isEmpty && ln.isEmpty then
        return txt
      else
        return txt ++ ln ++ "\n"
    unless txt.isEmpty do
      logInfo s!"stdout:\n{txt}"
  unless out.stderr.isEmpty do
    logInfo s!"stderr:\n{out.stderr}"
  if out.exitCode ≠ 0 then
    error s!"Lean exited with code {out.exitCode}"

def compileO
  (oFile srcFile : FilePath)
  (moreArgs : Array String := #[]) (compiler : FilePath := "cc")
: LogIO Unit := do
  createParentDirs oFile
  proc {
    cmd := compiler.toString
    args := #["-c", "-o", oFile.toString, srcFile.toString] ++ moreArgs
  }

def compileStaticLib
  (libFile : FilePath) (oFiles : Array FilePath)
  (ar : FilePath := "ar")
: LogIO Unit := do
  createParentDirs libFile
  proc {
    cmd := ar.toString
    args := #["rcs", libFile.toString] ++ oFiles.map toString
  }

def compileSharedLib
  (libFile : FilePath) (linkArgs : Array String)
  (linker : FilePath := "cc")
: LogIO Unit := do
  createParentDirs libFile
  proc {
    cmd := linker.toString
    args := #["-shared", "-o", libFile.toString] ++ linkArgs
  }

def compileExe
  (binFile : FilePath) (linkFiles : Array FilePath)
  (linkArgs : Array String := #[]) (linker : FilePath := "cc")
: LogIO Unit := do
  createParentDirs binFile
  proc {
    cmd := linker.toString
    args := #["-o", binFile.toString] ++ linkFiles.map toString ++ linkArgs
  }

/-- Download a file using `curl`, clobbering any existing file. -/
def download
  (url : String) (file : FilePath) (headers : Array String := #[])
: LogIO PUnit := do
  if (← file.pathExists) then
    IO.FS.removeFile file
  else
    createParentDirs file
  let args := #["-s", "-S", "-f", "-o", file.toString, "-L", url]
  let args := headers.foldl (init := args) (· ++ #["-H", ·])
  proc (quiet := true) {cmd := "curl", args}

/-- Unpack an archive `file` using `tar` into the directory `dir`. -/
def untar (file : FilePath) (dir : FilePath) (gzip := true) : LogIO PUnit := do
  IO.FS.createDirAll dir
  let mut opts := "-xvv"
  if gzip then
    opts := opts.push 'z'
  proc (quiet := true) {
    cmd := "tar",
    args := #[opts, "-f", file.toString, "-C", dir.toString]
  }

/-- Pack a directory `dir` using `tar` into the archive `file`. -/
def tar
  (dir : FilePath) (file : FilePath)
  (gzip := true) (excludePaths : Array FilePath := #[])
: LogIO PUnit := do
  createParentDirs file
  let mut args := #["-cvv"]
  if gzip then
    args := args.push "-z"
  for path in excludePaths do
    args := args.push s!"--exclude={path}"
  proc (quiet := true) {
    cmd := "tar"
    args := args ++ #["-f", file.toString, "-C", dir.toString, "."]
    -- don't pack `._` files on MacOS
    env := if Platform.isOSX then #[("COPYFILE_DISABLE", "true")] else #[]
  }
