/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Proc

namespace Lake
open System

def createParentDirs (path : FilePath) : IO Unit :=
  if let some dir := path.parent then IO.FS.createDirAll dir else pure ()

def compileOleanAndC (leanFile oleanFile cFile : FilePath)
(leanPath : String := "") (rootDir : FilePath := ".") (leanArgs : Array String := #[])
: IO Unit := do
  createParentDirs cFile
  createParentDirs oleanFile
  execCmd {
    cmd := "lean"
    args := leanArgs ++ #[
      "-R", rootDir.toString, "-o", oleanFile.toString, "-c",
      cFile.toString, leanFile.toString
    ]
    env := #[("LEAN_PATH", leanPath)]
  }

def compileO (oFile cFile : FilePath)
(leancArgs : Array String := #[]) : IO Unit := do
  createParentDirs oFile
  execCmd {
    cmd := "leanc"
    args := #["-c", "-o", oFile.toString, cFile.toString] ++ leancArgs
  }

def compileStaticLib
(libFile : FilePath) (oFiles : Array FilePath) : IO Unit := do
  createParentDirs libFile
  execCmd {
    cmd := "ar"
    args := #["rcs", libFile.toString] ++ oFiles.map toString
  }

def compileBin (binFile : FilePath)
(linkFiles : Array FilePath) (linkArgs : Array String := #[]) : IO Unit := do
  createParentDirs binFile
  execCmd {
    cmd := "leanc"
    args := #["-o", binFile.toString] ++ linkFiles.map toString ++ linkArgs
  }
