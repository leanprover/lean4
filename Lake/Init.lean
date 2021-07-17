/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Lake.Git
import Lake.LeanConfig

namespace Lake

def initGitignoreContents :=
"/build
"

def mainFileContents :=
"def main : IO Unit :=
  IO.println \"Hello, world!\"
"

def leanPkgFileContents (pkgName : String) :=
s!"import Lake.Package

def package : Lake.PackageConfig := \{
  name := \"{pkgName}\"
  version := \"0.1\"
  leanVersion := \"{leanVersionString}\"
}
"

open Git System

def initPkg (dir : FilePath) (pkgName : String) : IO PUnit := do
  IO.FS.writeFile (dir / leanPkgFile) (leanPkgFileContents pkgName)
  IO.FS.writeFile (dir / s!"{pkgName.capitalize}.lean") mainFileContents
  let h ← IO.FS.Handle.mk (dir / ".gitignore") IO.FS.Mode.append (bin := false)
  h.putStr initGitignoreContents
  unless ← FilePath.isDir (dir /".git") do
    try
      quietInit
      unless upstreamBranch = "master" do
        checkoutBranch upstreamBranch
    catch _ =>
      IO.eprintln "WARNING: failed to initialize git repository"

def init (pkgName : String) : IO PUnit :=
  initPkg "." pkgName

def new (pkgName : String) : IO PUnit := do
  IO.FS.createDir pkgName
  initPkg pkgName pkgName
