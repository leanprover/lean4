/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Elab.Frontend
import Lake.Package

open Lean System

namespace Lake

def leanPkgFile : FilePath := "package.lean"

namespace PackageConfig

unsafe def fromLeanFileUnsafe (path : FilePath) : IO PackageConfig := do
  let input ← IO.FS.readFile path
  let (env, ok) ← Elab.runFrontend input Options.empty path.toString `package
  if ok then
    IO.ofExcept <| Id.run <| ExceptT.run <|
      env.evalConstCheck PackageConfig Options.empty ``PackageConfig `package
  else
    throw <| IO.userError <| s!"package configuration (at {path}) has errors"

@[implementedBy fromLeanFileUnsafe]
constant fromLeanFile (path : FilePath) : IO PackageConfig
