/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Proc

namespace Lake
open System

def compileOleanAndC
(leanFile oleanFile cFile : FilePath) 
(leanPath : String := "") (rootDir : FilePath := ".") (leanArgs : Array String := #[])
: IO Unit := do
  if let some dir := cFile.parent then IO.FS.createDirAll dir
  if let some dir := oleanFile.parent then IO.FS.createDirAll dir
  execCmd {
    cmd := "lean"
    args := leanArgs ++ #[
      "-R", rootDir.toString, "-o", oleanFile.toString, "-c",  
      cFile.toString, leanFile.toString
    ]
    env := #[("LEAN_PATH", leanPath)]
  }

def compileO
(oFile cFile : FilePath) (leancArgs : Array String := #[])
: IO Unit := do
  if let some dir := oFile.parent then IO.FS.createDirAll dir
  execCmd {
    cmd := "leanc"
    args := #["-c", "-o", oFile.toString, cFile.toString] ++ leancArgs
  }

def compileBin
(binFile : FilePath) (oFiles : Array FilePath) (linkArgs : Array String := #[])
: IO Unit := do
  if let some dir := binFile.parent then IO.FS.createDirAll dir
  execCmd {
    cmd := "leanc"
    args := #["-o", binFile.toString] ++ oFiles.map toString ++ linkArgs
  }

def compileLib
(libFile : FilePath) (oFiles : Array FilePath)
: IO Unit := do
  if let some dir := libFile.parent then IO.FS.createDirAll dir
  execCmd {
    cmd := "ar"
    args := #["rcs", libFile.toString] ++ oFiles.map toString
  }
