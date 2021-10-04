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
    srcTarget.mapAsync fun file trace => do
      unless (← checkIfNewer oFile trace.mtime) do
        compileO oFile file args cmd
      trace

def staticLibTarget
(libFile : FilePath) (oFileTargets : Array FileTarget) (cmd := "ar") : FileTarget :=
  Target.mk libFile do
    let depTarget ← Target.collectArray oFileTargets
    depTarget.mapAsync fun oFiles trace => do
      unless (← checkIfNewer libFile trace.mtime) do
        compileStaticLib libFile oFiles cmd
      trace

def binTarget
(binFile : FilePath) (linkTargets : Array FileTarget)
(linkArgs : Array String := #[]) (cmd := "cc") : FileTarget :=
  Target.mk binFile do
    let depTarget ← Target.collectArray linkTargets
    depTarget.mapAsync fun links trace => do
      unless (← checkIfNewer binFile trace.mtime) do
        compileBin binFile links linkArgs cmd
      trace
