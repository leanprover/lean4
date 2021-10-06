/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Compile
import Lake.BuildTarget

open System
namespace Lake

def buildFileUnlessUpToDate (file : FilePath)
(trace : BuildTrace) (build : BuildM PUnit) : BuildM BuildTrace := do
  let traceFile := FilePath.mk <| file.toString ++ ".trace"
  let (upToDate, trace) ← trace.check file traceFile
  unless upToDate do
    build
  IO.FS.writeFile traceFile trace.hash.toString
  liftM <| computeTrace file

def oFileTarget (oFile : FilePath) (srcTarget : FileTarget)
(args : Array String := #[]) (compiler : FilePath := "c++") : FileTarget :=
  Target.mk oFile do
    srcTarget.mapAsync fun file trace => do
      buildFileUnlessUpToDate oFile trace do
        compileO oFile file args compiler

def leanOFileTarget (oFile : FilePath)
(srcTarget : FileTarget) (args : Array String := #[]) : FileTarget :=
  Target.mk oFile do
    srcTarget.mapAsync fun file trace => do
      buildFileUnlessUpToDate oFile trace do
        compileO oFile file args (← getLeanc)

def staticLibTarget (libFile : FilePath)
(oFileTargets : Array FileTarget) (ar : FilePath := "ar") : FileTarget :=
  Target.mk libFile do
    Target.collectArray oFileTargets |>.mapAsync fun oFiles trace => do
      buildFileUnlessUpToDate libFile trace do
        compileStaticLib libFile oFiles ar

def binTarget (binFile : FilePath) (linkTargets : Array FileTarget)
(linkArgs : Array String := #[]) (linker : FilePath := "cc") : FileTarget :=
  Target.mk binFile do
    Target.collectArray linkTargets |>.mapAsync fun links trace => do
      buildFileUnlessUpToDate binFile trace do
        compileBin binFile links linkArgs linker

def leanBinTarget (binFile : FilePath) (linkTargets : Array FileTarget)
(linkArgs : Array String := #[]) (linker : FilePath := "cc") : FileTarget :=
  Target.mk binFile do
    Target.collectArray linkTargets |>.mapAsync fun links trace => do
      buildFileUnlessUpToDate binFile trace do
        compileBin binFile links linkArgs (← getLeanc)
