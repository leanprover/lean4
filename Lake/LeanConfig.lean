/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Elab.Frontend
import Lake.Package

open Lean System

namespace Lake

def pkgModName : Name := `package
def pkgDefName : Name := `package
def pkgFileName : FilePath := "package.lean"

namespace Package

unsafe def fromLeanFileUnsafe
(path : FilePath) (root : FilePath) (args : List String := [])
: IO Package := do
  let input ← IO.FS.readFile path
  let (env, ok) ← Elab.runFrontend input Options.empty path.toString pkgModName
  if ok then
    let ioPackagerE := Id.run <| ExceptT.run <|
      env.evalConstCheck IOPackager Options.empty ``IOPackager pkgDefName
    match ioPackagerE with
    | Except.ok packager => Package.mk root (← packager root args)
    | Except.error error =>
    let packagerE := Id.run <| ExceptT.run <|
      env.evalConstCheck Packager Options.empty ``Packager pkgDefName
    match packagerE with
    | Except.ok packager => Package.mk root (← packager root args)
    | Except.error error =>
    let configE := Id.run <| ExceptT.run <|
      env.evalConstCheck PackageConfig Options.empty ``PackageConfig pkgDefName
    match configE with
    | Except.ok config => Package.mk root config
    | Except.error error => throw <| IO.userError <|
      s!"unexpected type at 'package', `Lake.IOPackager`, `Lake.Packager`, or `Lake.PackageConfig` expected"
  else
    throw <| IO.userError <| s!"package configuration (at {path}) has errors"

@[implementedBy fromLeanFileUnsafe]
constant fromLeanFile (path : FilePath) (root : FilePath) (args : List String := []) : IO Package

unsafe def fromDirUnsafe
(dir : FilePath) (args : List String := []) (file := pkgFileName) : IO Package :=
  fromLeanFileUnsafe (dir / file) dir args

@[implementedBy fromDirUnsafe]
constant fromDir (dir : FilePath) (args : List String := []) (file := pkgFileName) : IO Package
