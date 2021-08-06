/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Compile
import Lake.BuildTarget

open System
namespace Lake

def oFileTarget
(oFile : FilePath) (srcTarget : FileTarget)
(args : Array String := #[]) (cmd := "c++") : FileTarget :=
  FileTarget.mk oFile srcTarget.trace <|
    unless (← checkIfNewer oFile srcTarget.mtime) do
      srcTarget.materialize
      compileO oFile srcTarget.file args (cmd := "c++")

def staticLibTarget
(libFile : FilePath) (oFilesTarget : FilesTarget) : FileTarget :=
  FileTarget.mk libFile oFilesTarget.trace do
    unless (← checkIfNewer libFile oFilesTarget.mtime) do
      oFilesTarget.materialize
      compileStaticLib libFile oFilesTarget.filesAsArray
