/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/

namespace Lake
open System

def createParentDirs (path : FilePath) : IO PUnit := do
  if let some dir := path.parent then
    try IO.FS.createDirAll dir catch e => IO.eprintln e

def proc (args : IO.Process.SpawnArgs) : IO PUnit := do
  let envStr := String.join <| args.env.toList.map fun (k, v) => s!"{k}={v.getD ""} "
  let cmdStr := " ".intercalate (args.cmd :: args.args.toList)
  IO.println <| "> " ++ envStr ++
    match args.cwd with
    | some cwd => s!"{cmdStr}    # in directory {cwd}"
    | none     => cmdStr
  let child ← IO.Process.spawn args
  let exitCode ← child.wait
  if exitCode != 0 then
    let msg := s!"external command exited with status {exitCode}"
    IO.eprintln msg -- print errors early
    throw <| IO.userError msg

def compileOleanAndC (leanFile oleanFile cFile : FilePath)
(leanPath : String := "") (rootDir : FilePath := ".") (leanArgs : Array String := #[])
: IO PUnit := do
  createParentDirs cFile
  createParentDirs oleanFile
  proc {
    cmd := "lean"
    args := leanArgs ++ #[
      "-R", rootDir.toString, "-o", oleanFile.toString, "-c",
      cFile.toString, leanFile.toString
    ]
    env := #[("LEAN_PATH", leanPath)]
  }

def compileO (oFile cFile : FilePath)
(moreArgs : Array String := #[]) (cmd := "cc") : IO PUnit := do
  createParentDirs oFile
  proc {
    cmd
    args := #["-c", "-o", oFile.toString, cFile.toString] ++ moreArgs
  }

def compileLeanO (oFile cFile : FilePath) (leancArgs : Array String := #[]) : IO PUnit :=
  compileO oFile cFile leancArgs "leanc"

def compileStaticLib
(libFile : FilePath) (oFiles : Array FilePath) : IO PUnit := do
  createParentDirs libFile
  proc {
    cmd := "ar"
    args := #["rcs", libFile.toString] ++ oFiles.map toString
  }

def compileBin (binFile : FilePath)
(linkFiles : Array FilePath) (linkArgs : Array String := #[]) (cmd := "cc") : IO PUnit := do
  createParentDirs binFile
  proc {
    cmd
    args := #["-o", binFile.toString] ++ linkFiles.map toString ++ linkArgs
  }

def compileLeanBin (binFile : FilePath)
(linkFiles : Array FilePath) (linkArgs : Array String := #[]) : IO PUnit :=
  compileBin binFile linkFiles linkArgs "leanc"
