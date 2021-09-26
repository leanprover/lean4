/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Lake.Git
import Lake.Package
import Lake.LeanConfig

namespace Lake
open Git System

/-- `elan` toolchain file name -/
def toolchainFileName : FilePath :=
"lean-toolchain"

def gitignoreContents :=
s!"/{defaultBuildDir}\n/{defaultDepsDir}\n"

def mainFileName (pkgName : String) : FilePath :=
  s!"{pkgName.capitalize}.lean"

def mainFileContents :=
"def main : IO Unit :=
  IO.println \"Hello, world!\"
"

def pkgFileContents (pkgName : String) :=
s!"import Lake
open Lake DSL

package \{
  name := \"{pkgName}\"
}
"

/-- Initialize a new Lake package in the given directory with the given name. -/
def initPkg (dir : FilePath) (name : String) : IO PUnit := do

  -- write default configuration file
  let pkgFile := dir / pkgFileName
  if (← pkgFile.pathExists) then
    -- error if package already has a `package.lean`
    throw <| IO.userError "package already initialized"
  IO.FS.writeFile pkgFile (pkgFileContents name)

  -- write example main module if none exists
  let mainFile := dir / mainFileName name
  unless (← mainFile.pathExists) do
    IO.FS.writeFile mainFile mainFileContents

  -- write current toolchain to file for `elan`
  IO.FS.writeFile (dir / toolchainFileName) <| leanVersionString ++ "\n"

  -- update `.gitignore`
  let h ← IO.FS.Handle.mk (dir / ".gitignore") IO.FS.Mode.append (bin := false)
  h.putStr gitignoreContents

  -- initialize a `.git` repository if none already
  unless (← FilePath.isDir <| dir / ".git") do
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
