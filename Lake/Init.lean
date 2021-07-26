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

def mainFileName (pkgName : String) : System.FilePath :=
  s!"{pkgName.capitalize}.lean"

def mainFileContents :=
"def main : IO Unit :=
  IO.println \"Hello, world!\"
"

def pkgFileContents (pkgName : String) :=
s!"import Lake.Package

def package : Lake.PackageConfig := \{
  name := \"{pkgName}\"
  version := \"0.1\"
  leanVersion := \"{leanVersionString}\"
}
"

open Git System

def initPkg (dir : FilePath) (pkgName : String) : IO PUnit := do
  IO.FS.writeFile (dir / pkgFileName) (pkgFileContents pkgName)
  IO.FS.writeFile (dir / mainFileName pkgName) mainFileContents
  let h ← IO.FS.Handle.mk (dir / ".gitignore") IO.FS.Mode.append (bin := false)
  h.putStr initGitignoreContents
  unless ← FilePath.isDir (dir /".git") do
    try
      quietInit dir
      unless upstreamBranch = "master" do
        checkoutBranch upstreamBranch dir
    catch _ =>
      IO.eprintln "WARNING: failed to initialize git repository"

def init (pkgName : String) : IO PUnit :=
  initPkg "." pkgName

def new (pkgName : String) : IO PUnit := do
  IO.FS.createDir pkgName
  initPkg pkgName pkgName
