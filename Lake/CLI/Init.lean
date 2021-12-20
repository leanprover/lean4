/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Lake.Util.Git
import Lake.Config.Package
import Lake.Config.Load

namespace Lake
open Git System
open Lean (Name)

/-- `elan` toolchain file name -/
def toolchainFileName : FilePath :=
"lean-toolchain"

def gitignoreContents :=
s!"/{defaultBuildDir}\n/{defaultPackagesDir}\n"

def libFileContents :=
  s!"def hello := \"world\""

def mainFileName : FilePath :=
  s!"{defaultBinRoot}.lean"

def mainFileContents (libRoot : Name) :=
s!"import {libRoot}

def main : IO Unit :=
  IO.println s!\"Hello, \{hello}!\"
"

def pkgConfigFileContents (pkgName : String) :=
s!"import Lake
open Lake DSL

package {pkgName.toName} \{
  -- add configuration options here
}
"

/-- Initialize a new Lake package in the given directory with the given name. -/
def initPkg (dir : FilePath) (name : String) : IO PUnit := do

  -- write default configuration file
  let configFile := dir / defaultConfigFile
  if (← configFile.pathExists) then
    -- error if package already has a `lakefile.lean`
    throw <| IO.userError "package already initialized"
  IO.FS.writeFile configFile (pkgConfigFileContents name)

  -- write example code if the files do not already exist
  let libRoot := toUpperCamelCase name.toName
  let libFile := Lean.modToFilePath dir libRoot "lean"
  unless (← libFile.pathExists) do
    IO.FS.createDirAll libFile.parent.get!
    IO.FS.writeFile libFile libFileContents
  let mainFile := dir / mainFileName
  unless (← mainFile.pathExists) do
    IO.FS.writeFile mainFile <| mainFileContents libRoot

  -- write Lean's toolchain to file (if it has one) for `elan`
  if Lean.toolchain ≠ "" then
    IO.FS.writeFile (dir / toolchainFileName) <| Lean.toolchain ++ "\n"

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
  let dirName := pkgName.map fun chr => if chr == '.' then '-' else chr
  IO.FS.createDir dirName
  initPkg dirName pkgName
