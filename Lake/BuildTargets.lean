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
  Target.mk oFile do
    srcTarget.mapAsync fun file srcTrace => do
      unless (← checkIfNewer oFile srcTrace.mtime) do
        compileO oFile file args cmd
      srcTrace

def staticLibTarget
(libFile : FilePath) (oFileTargets : Array FileTarget) : FileTarget :=
  Target.mk libFile do
    let oFilesTarget ← Target.collectArray oFileTargets
    oFilesTarget.mapAsync fun files trace => do
      unless (← checkIfNewer libFile trace.mtime) do
        compileStaticLib libFile files
      trace
