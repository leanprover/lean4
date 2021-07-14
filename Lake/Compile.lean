/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Lake.BuildTarget

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
    IO.eprintln s!"external command exited with status {exitCode}"

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
(leancArgs : Array String := #[]) : IO PUnit := do
  createParentDirs oFile
  proc {
    cmd := "leanc"
    args := #["-c", "-o", oFile.toString, cFile.toString] ++ leancArgs
  }

def compileStaticLib
(libFile : FilePath) (oFiles : Array FilePath) : IO PUnit := do
  createParentDirs libFile
  proc {
    cmd := "ar"
    args := #["rcs", libFile.toString] ++ oFiles.map toString
  }

def compileBin (binFile : FilePath)
(linkFiles : Array FilePath) (linkArgs : Array String := #[]) : IO PUnit := do
  createParentDirs binFile
  proc {
    cmd := "leanc"
    args := #["-o", binFile.toString] ++ linkFiles.map toString ++ linkArgs
  }
