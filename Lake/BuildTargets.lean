/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Compile
import Lake.Target

open System
namespace Lake

def oFileTarget
(oFile : FilePath) (srcTarget : FileTarget)
(args : Array String := #[]) (cmd := "c++") : FileTarget :=
  Target.mk oFile srcTarget.trace <|
    unless (← checkIfNewer oFile srcTarget.mtime) do
      srcTarget >> compileO oFile srcTarget.file args cmd

def staticLibTarget
(libFile : FilePath) (oFileTargets : Array FileTarget) : FileTarget :=
  let linkFiles := oFileTargets.map (·.artifact)
  let trace := mixTraceArray <| oFileTargets.map (·.trace)
  Target.mk libFile trace do
    unless (← checkIfNewer libFile trace.mtime) do
      oFileTargets >> compileStaticLib libFile linkFiles
