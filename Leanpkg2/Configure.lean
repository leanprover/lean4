/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Leanpkg2.BuildCore
import Leanpkg2.Resolve

open System

namespace Leanpkg2

def getRootPart (pkg : FilePath := ".") : IO Lean.Name := do
  let entries ← pkg.readDir
  match entries.filter (FilePath.extension ·.fileName == "lean") with
  | #[rootFile] => FilePath.withExtension rootFile.fileName "" |>.toString
  | #[]         => throw <| IO.userError s!"no '.lean' file found in {← IO.realPath "."}"
  | _           => throw <| IO.userError s!"{← IO.realPath "."} must contain a unique '.lean' file as the package root"

structure Configuration :=
  leanPath    : String
  leanSrcPath : String
  moreDeps    : List FilePath

def configure (manifest : Manifest) : IO Configuration := do
  IO.eprintln $
    "configuring " ++ manifest.name ++ " " ++ manifest.version
  let paths ← solveDeps manifest
  let mut moreDeps := []
  for (pkgpath, srcpath) in paths do
    unless pkgpath == "." do
      -- build recursively
      -- TODO: share build of common dependencies
      execCmd {
        cmd := (← IO.appPath).toString
        cwd := pkgpath
        args := #["build"]
      }
      let pkgRoot := srcpath / Build.buildPath / (← getRootPart srcpath).toString
      moreDeps := pkgRoot.withExtension "olean" :: moreDeps
  return {
    leanPath    := SearchPath.toString <| paths.map (·.2 / Build.buildPath)
    leanSrcPath := SearchPath.toString <| paths.map (·.2)
    moreDeps
  }
