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
    let traceFile := FilePath.mk <| oFile.toString ++ ".trace"
    srcTarget.mapAsync fun file trace => do
      let (upToDate, trace) ← trace.check oFile traceFile
      unless upToDate do
        compileO oFile file args cmd
      IO.FS.writeFile traceFile trace.hash.toString
      liftM <| computeTrace oFile

def staticLibTarget
(libFile : FilePath) (oFileTargets : Array FileTarget) (cmd := "ar") : FileTarget :=
  Target.mk libFile do
    let traceFile := FilePath.mk <| libFile.toString ++ ".trace"
    let depTarget ← Target.collectArray oFileTargets
    depTarget.mapAsync fun oFiles trace => do
      let (upToDate, trace) ← trace.check libFile traceFile
      unless upToDate do
        compileStaticLib libFile oFiles cmd
      IO.FS.writeFile traceFile trace.hash.toString
      liftM <| computeTrace libFile

def binTarget
(binFile : FilePath) (linkTargets : Array FileTarget)
(linkArgs : Array String := #[]) (cmd := "cc") : FileTarget :=
  Target.mk binFile do
    let traceFile := FilePath.mk <| binFile.toString ++ ".trace"
    let depTarget ← Target.collectArray linkTargets
    depTarget.mapAsync fun links trace => do
      let (upToDate, trace) ← trace.check binFile traceFile
      unless upToDate do
        compileBin binFile links linkArgs cmd
      IO.FS.writeFile traceFile trace.hash.toString
      liftM <| computeTrace binFile
