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
  -- Enables the use of the Lean interpreter by the executable (e.g.,
  -- `runFrontend`) at the expense of increased binary size on Linux.
  -- Remove this line if you do not need such functionality.
  supportInterpreter := true
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

def moreServerArgs := #[
  \"-Dpp.unicode.fun=true\", -- pretty-prints `fun a ↦ b`
  \"-Dpp.proofs.withType=false\"
]

-- These settings only apply during `lake build`, but not in VSCode editor.
def moreLeanArgs := moreServerArgs

-- These are additional settings which do not affect the lake hash,
-- so they can be enabled in CI and disabled locally or vice versa.
-- Warning: Do not put any options here that actually change the olean files,
-- or inconsistent behavior may result
def weakLeanArgs : Array String :=
  if get_config? CI |>.isSome then
    #[\"-DwarningAsError=true\"]
  else
    #[]

package {pkgName} where
  moreServerArgs := moreServerArgs
  -- add any package configuration options here

require mathlib from git
  \"https://github.com/leanprover-community/mathlib4.git\"

@[default_target]
lean_lib {libRoot} where
  moreLeanArgs := moreLeanArgs
  weakLeanArgs := weakLeanArgs
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

def InitTemplate.configFileContents (pkgName root : String) : InitTemplate → String
| .std => stdConfigFileContents pkgName root pkgName.toLower
| .lib => libConfigFileContents pkgName root
| .exe => exeConfigFileContents pkgName root
| .math => mathConfigFileContents pkgName root

def escapeName! : Name → String
| .anonymous        => "[anonymous]"
| .str .anonymous s => escape s
| .str n s          => escapeName! n ++ "." ++ escape s
| _                 => unreachable!
where
  escape s :=  Lean.idBeginEscape.toString ++ s ++ Lean.idEndEscape.toString

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
      let root := toUpperCamelCase (toUpperCamelCaseString name |>.toName)
      let rootFile := Lean.modToFilePath dir root "lean"
      pure (root, rootFile, ← rootFile.pathExists)

  -- write default configuration file
  let configFile := dir / defaultConfigFile
  if (← configFile.pathExists) then
    error  "package already initialized"
  let rootNameStr := escapeName! root
  let contents := tmp.configFileContents (escapeName! pkgName) rootNameStr
  IO.FS.writeFile configFile contents

  -- write example code if the files do not already exist
  if tmp = .exe then
    unless (← rootFile.pathExists) do
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

def init (pkgName : String) (tmp : InitTemplate) (env : Lake.Env) : LogIO PUnit :=
  initPkg "." pkgName tmp env

def new (pkgName : String) (tmp : InitTemplate) (env : Lake.Env) : LogIO PUnit := do
  let dirName := pkgName.map fun chr => if chr == '.' then '-' else chr
  IO.FS.createDir dirName
  initPkg dirName pkgName tmp env
