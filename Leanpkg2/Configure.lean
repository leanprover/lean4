/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Leanpkg2.BuildConfig
import Leanpkg2.Resolve

open System

namespace Leanpkg2

structure Configuration :=
  leanPath    : String
  leanSrcPath : String
  moreDeps    : List FilePath

def configure (manifest : Manifest) : IO Configuration := do
  IO.eprintln $ "configuring " ++ manifest.name ++ " " ++ manifest.version
  let pkgs ← solveDeps manifest
  let mut moreDeps := []
  for pkg in pkgs do
    unless pkg.dir.toString == "." do
      -- build recursively
      -- TODO: share build of common dependencies
      execCmd {
        cwd := pkg.dir
        cmd := (← IO.appDir) / "lean" |>.toString
        args := #["--run", "Package.lean"]
      }
      moreDeps := pkg.buildRoot.withExtension "olean" :: moreDeps
  return {
    leanPath    := SearchPath.toString <| pkgs.map (·.buildDir)
    leanSrcPath := SearchPath.toString <| pkgs.map (·.sourceDir)
    moreDeps
  }
