/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Lake.Util.Git
import Lake.Util.Sugar
import Lake.Config.Package
import Lake.Config.Workspace
import Lake.Load.Config
import Lake.Build.Actions

namespace Lake
open Git System

/-- The default module of an executable in `std` package. -/
def defaultExeRoot : Name := `Main

def gitignoreContents :=
s!"/{defaultLakeDir}
"

def basicFileContents :=
  s!"def hello := \"world\""

def libRootFileContents (libName : String) (libRoot : String) :=
s!"-- This module serves as the root of the `{libName}` library.
-- Import modules here that should be built as part of the library.
import {libRoot}.Basic"

def mainFileName : FilePath :=
  s!"{defaultExeRoot}.lean"

def mainFileContents (libRoot : String) :=
s!"import {libRoot}

def main : IO Unit :=
  IO.println s!\"Hello, \{hello}!\"
"

def exeFileContents :=
s!"def main : IO Unit :=
  IO.println s!\"Hello, world!\"
"

def stdConfigFileContents (pkgName libRoot exeName : String) :=
s!"import Lake
open Lake DSL

package {pkgName} where
  -- add package configuration options here

lean_lib {libRoot} where
  -- add library configuration options here

@[default_target]
lean_exe {exeName} where
  root := `Main
"

def exeConfigFileContents (pkgName exeRoot : String) :=
s!"import Lake
open Lake DSL

package {pkgName} where
  -- add package configuration options here

@[default_target]
lean_exe {exeRoot} where
  -- Enables the use of the Lean interpreter by the executable (e.g.,
  -- `runFrontend`) at the expense of increased binary size on Linux.
  -- Remove this line if you do not need such functionality.
  supportInterpreter := true
"

def libConfigFileContents (pkgName libRoot : String) :=
s!"import Lake
open Lake DSL

package {pkgName} where
  -- add package configuration options here

@[default_target]
lean_lib {libRoot} where
  -- add library configuration options here
"

def mathConfigFileContents (pkgName libRoot : String) :=
s!"import Lake
open Lake DSL

package {pkgName} where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩
  ]
  -- add any additional package configuration options here

require mathlib from git
  \"https://github.com/leanprover-community/mathlib4.git\"

@[default_target]
lean_lib {libRoot} where
  -- add any library configuration options here
"

def mathToolchainUrl : String :=
  "https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain"

/-- The options for the template argument to `initPkg`. -/
inductive InitTemplate
| std | exe | lib | math
deriving Repr, DecidableEq

instance : Inhabited InitTemplate := ⟨.std⟩

def InitTemplate.parse? : String → Option InitTemplate
| "std" => some .std
| "exe" => some .exe
| "lib" => some .lib
| "math" => some .math
| _ => none

def escapeIdent (id : String) : String :=
  Lean.idBeginEscape.toString ++ id ++ Lean.idEndEscape.toString

def escapeName! : Name → String
| .anonymous        => unreachable!
| .str .anonymous s => escapeIdent s
| .str n s          => escapeName! n ++ "." ++ escapeIdent s
| _                 => unreachable!

def InitTemplate.configFileContents (pkgName : Name) (root : String) : InitTemplate → String
| .std => stdConfigFileContents (escapeName! pkgName) root
  (escapeIdent <| pkgName.toStringWithSep "-" false).toLower
| .lib => libConfigFileContents (escapeName! pkgName) root
| .exe => exeConfigFileContents (escapeName! pkgName) root
| .math => mathConfigFileContents (escapeName! pkgName) root

/-- Initialize a new Lake package in the given directory with the given name. -/
def initPkg (dir : FilePath) (name : String) (tmp : InitTemplate) (env : Lake.Env) : LogIO PUnit := do
  let pkgName := stringToLegalOrSimpleName name

  -- determine the name to use for the root
  -- use upper camel case unless the specific module name already exists
  let (root, rootFile, rootExists) ← do
    let root := pkgName
    let rootFile := Lean.modToFilePath dir root "lean"
    let rootExists ← rootFile.pathExists
    if tmp = .exe || rootExists then
      pure (root, rootFile, rootExists)
    else
      let root := toUpperCamelCase pkgName
      let rootFile := Lean.modToFilePath dir root "lean"
      pure (root, rootFile, ← rootFile.pathExists)

  -- write default configuration file
  let configFile := dir / defaultConfigFile
  if (← configFile.pathExists) then
    error  "package already initialized"
  let rootNameStr := escapeName! root
  let contents := tmp.configFileContents pkgName rootNameStr
  IO.FS.writeFile configFile contents

  -- write example code if the files do not already exist
  if tmp = .exe then
    unless (← rootFile.pathExists) do
      createParentDirs rootFile
      IO.FS.writeFile rootFile exeFileContents
  else
    unless rootExists do
      let libDir := rootFile.withExtension ""
      let basicFile := libDir / "Basic.lean"
      unless (← basicFile.pathExists) do
        IO.FS.createDirAll libDir
        IO.FS.writeFile basicFile basicFileContents
      let rootContents := libRootFileContents root.toString rootNameStr
      IO.FS.writeFile rootFile rootContents
    if tmp = .std then
      let mainFile := dir / mainFileName
      unless (← mainFile.pathExists) do
        IO.FS.writeFile mainFile <| mainFileContents rootNameStr

  /-
  Write the detected toolchain to file (if there is one) for `elan`.
  See [lean4#2518][1] for details on the design considerations taken here.

  [1]: https://github.com/leanprover/lean4/issues/2518
  -/
  let toolchainFile := dir / toolchainFileName
  if env.toolchain.isEmpty then
    -- Empty githash implies dev build
    unless env.lean.githash.isEmpty do
      unless (← toolchainFile.pathExists) do
        logWarning <|
          "could not create a `lean-toolchain` file for the new package; "  ++
          "no known toolchain name for the current Elan/Lean/Lake"
  else
    if tmp = .math then
      download "lean-toolchain" mathToolchainUrl toolchainFile
    else
      IO.FS.writeFile toolchainFile <| env.toolchain ++ "\n"

  -- update `.gitignore` with additional entries for Lake
  let h ← IO.FS.Handle.mk (dir / ".gitignore") IO.FS.Mode.append
  h.putStr gitignoreContents

  -- initialize a `.git` repository if none already
  unless (← FilePath.isDir <| dir / ".git") do
    let repo := GitRepo.mk dir
    try
      repo.quietInit
      unless upstreamBranch = "master" do
        repo.checkoutBranch upstreamBranch
    else
      logWarning "failed to initialize git repository"

def validatePkgName (pkgName : String) : LogIO PUnit := do
  if pkgName.isEmpty || pkgName.all (· == '.') || pkgName.any (· ∈ ['/', '\\']) then
    error "illegal package name"
  if pkgName.toLower ∈ ["init", "lean", "lake", "main"] then
    error "reserved package name"

def init (pkgName : String) (tmp : InitTemplate) (env : Lake.Env) (cwd : FilePath := ".") : LogIO PUnit := do
  let pkgName ← do
    if pkgName == "." then
      match (← IO.FS.realPath cwd).fileName with
      | some dirName => pure dirName
      | none => error "illegal package name"
    else
      pure pkgName
  let pkgName := pkgName.trim
  validatePkgName pkgName
  IO.FS.createDirAll cwd
  initPkg cwd pkgName tmp env

def new (pkgName : String) (tmp : InitTemplate) (env : Lake.Env) (cwd : FilePath := ".") : LogIO PUnit := do
  let pkgName := pkgName.trim
  validatePkgName pkgName
  let dirName := cwd / pkgName.map fun chr => if chr == '.' then '-' else chr
  IO.FS.createDirAll dirName
  initPkg dirName pkgName tmp env
