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

namespace Package

unsafe def fromLeanFileUnsafe
(path : FilePath) (root : FilePath) (args : List String := [])
: IO Package := do
  let input ← IO.FS.readFile path
  let (env, ok) ← Elab.runFrontend input Options.empty path.toString `package
  if ok then
    let packagerE := Id.run <| ExceptT.run <|
        env.evalConstCheck Packager Options.empty ``Packager `package
    match packagerE with
    | Except.ok packager => Package.mk root (← packager root args)
    | Except.error error =>
      let configE := Id.run <| ExceptT.run <|
        env.evalConstCheck PackageConfig Options.empty ``PackageConfig `package
      match configE with
      | Except.ok config => Package.mk root config
      | Except.error error => throw <| IO.userError <|
        s!"unexpected type at 'package', `Lake.Packager` or `Lake.PackageConfig` expected"
  else
    throw <| IO.userError <| s!"package configuration (at {path}) has errors"

unsafe def fromDirUnsafe
(path : FilePath) (args : List String := []) : IO Package :=
  fromLeanFileUnsafe (path / leanPkgFile) path args

@[implementedBy fromDirUnsafe]
constant fromDir (path : FilePath) (args : List String := []) : IO Package
