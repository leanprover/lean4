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

/-- The default name of the Lake configuration file (i.e., `lakefile.lean`). -/
def defaultConfigFile : FilePath := "lakefile.lean"

namespace Package

unsafe def fromLeanFileUnsafe
(path : FilePath) (dir : FilePath) (args : List String := [])
: IO Package := do
  let opts := Options.empty
  let input ← IO.FS.readFile path
  let (env, ok) ← Elab.runFrontend input opts path.toString pkgModName
  if ok then
    let m := env.evalConstCheck IOPackager opts ``IOPackager pkgDefName
    if let Except.ok ioPackager := m.run.run then
      return Package.mk dir (← ioPackager dir args)
    let m := env.evalConstCheck Packager opts ``Packager pkgDefName
    if let Except.ok packager := m.run.run then
      return Package.mk dir (packager dir args)
    let m := env.evalConstCheck PackageConfig opts ``PackageConfig pkgDefName
    if let Except.ok config := m.run.run then
      return Package.mk dir config
    throw <| IO.userError
      s!"unexpected type at 'package', `Lake.IOPackager`, `Lake.Packager`, or `Lake.PackageConfig` expected"
  else
    throw <| IO.userError s!"package configuration (at {path}) has errors"

@[implementedBy fromLeanFileUnsafe]
constant fromLeanFile (path : FilePath) (dir : FilePath) (args : List String := []) : IO Package

unsafe def fromDirUnsafe
(dir : FilePath) (args : List String := []) (file := defaultConfigFile) : IO Package :=
  fromLeanFileUnsafe (dir / file) dir args

@[implementedBy fromDirUnsafe]
constant fromDir (dir : FilePath) (args : List String := []) (file := defaultConfigFile) : IO Package
