/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Lake.Util.Git
import Lake.Util.Sugar
import Lake.Util.Version
import Lake.Config.Lang
import Lake.Config.Package
import Lake.Config.Workspace
import Lake.Load.Config
import Lake.Build.Actions

namespace Lake
open Git System
open Lean (Name)

/-- The default module of an executable in `std` package. -/
def defaultExeRoot : Name := `Main

def gitignoreContents :=
s!"/{defaultLakeDir}
"

def basicFileContents :=
  s!"def hello := \"world\""

def libRootFileContents (libName : String) (libRoot : Name) :=
s!"-- This module serves as the root of the `{libName}` library.
-- Import modules here that should be built as part of the library.
import {libRoot}.Basic"

def mainFileName : FilePath :=
  s!"{defaultExeRoot}.lean"

def mainFileContents (libRoot : Name) :=
s!"import {libRoot}

def main : IO Unit :=
  IO.println s!\"Hello, \{hello}!\"
"

def exeFileContents :=
s!"def main : IO Unit :=
  IO.println s!\"Hello, world!\"
"

def stdLeanConfigFileContents (pkgName libRoot exeName : String) :=
s!"import Lake
open Lake DSL

package {repr pkgName} where
  version := v!\"0.1.0\"

lean_lib {libRoot} where
  -- add library configuration options here

@[default_target]
lean_exe {repr exeName} where
  root := `Main
"

def stdTomlConfigFileContents (pkgName libRoot exeName : String) :=
s!"name = {repr pkgName}
version = \"0.1.0\"
defaultTargets = [{repr exeName}]

[[lean_lib]]
name = {repr libRoot}

[[lean_exe]]
name = {repr exeName}
root = \"Main\"
"

def exeLeanConfigFileContents (pkgName exeName : String) :=
s!"import Lake
open Lake DSL

package {repr pkgName} where
  version := v!\"0.1.0\"

@[default_target]
lean_exe {repr exeName} where
  root := `Main
"

def exeTomlConfigFileContents (pkgName exeName : String) :=
s!"name = {repr pkgName}
version = \"0.1.0\"
defaultTargets = [{repr exeName}]

[[lean_exe]]
name = {repr exeName}
root = \"Main\"
"

def libLeanConfigFileContents (pkgName libRoot : String) :=
s!"import Lake
open Lake DSL

package {repr pkgName} where
  version := v!\"0.1.0\"

@[default_target]
lean_lib {libRoot} where
  -- add library configuration options here
"

def libTomlConfigFileContents (pkgName libRoot : String) :=
s!"name = {repr pkgName}
version = \"0.1.0\"
defaultTargets = [{repr libRoot}]

[[lean_lib]]
name = {repr libRoot}
"

def mathLeanConfigFileContents (pkgName libRoot : String) :=
s!"import Lake
open Lake DSL

package {repr pkgName} where
  version := v!\"0.1.0\"
  keywords := #[\"math\"]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩
  ]

require \"leanprover-community\" / \"mathlib\"

@[default_target]
lean_lib {libRoot} where
  -- add any library configuration options here
"

def mathTomlConfigFileContents (pkgName libRoot : String) :=
s!"name = {repr pkgName}
version = \"0.1.0\"
keywords = [\"math\"]
defaultTargets = [{repr libRoot}]

[leanOptions]
pp.unicode.fun = true # pretty-prints `fun a ↦ b`
autoImplicit = false

[[require]]
name = \"mathlib\"
scope = \"leanprover-community\"

[[lean_lib]]
name = {repr libRoot}
"

def readmeFileContents (pkgName : String) := s!"# {pkgName}"

def mathToolchainBlobUrl : String :=
  "https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain"

def mathToolchainUrl : String :=
  "https://github.com/leanprover-community/mathlib4/blob/master/lean-toolchain"

def leanActionWorkflowContents :=
"name: Lean Action CI

on:
  push:
  pull_request:
  workflow_dispatch:

jobs:
  build:
    runs-on: ubuntu-latest

    steps:
      - uses: actions/checkout@v4
      - uses: leanprover/lean-action@v1
"

/-- Lake package template identifier. -/
inductive InitTemplate
| std | exe | lib | math
deriving Repr, DecidableEq

instance : Inhabited InitTemplate := ⟨.std⟩

def InitTemplate.ofString? : String → Option InitTemplate
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

def dotlessName (name : Name) :=
  name.toString false |>.map fun chr => if chr == '.' then '-' else chr

def InitTemplate.configFileContents  (tmp : InitTemplate) (lang : ConfigLang) (pkgName : Name) (root : Name) : String :=
  let pkgNameStr := dotlessName pkgName
  match tmp, lang with
  | .std, .lean => stdLeanConfigFileContents pkgNameStr (escapeName! root) pkgNameStr.toLower
  | .std, .toml => stdTomlConfigFileContents pkgNameStr root.toString pkgNameStr.toLower
  | .lib, .lean => libLeanConfigFileContents pkgNameStr (escapeName! root)
  | .lib, .toml => libTomlConfigFileContents pkgNameStr root.toString
  | .exe, .lean => exeLeanConfigFileContents pkgNameStr pkgNameStr.toLower
  | .exe, .toml => exeTomlConfigFileContents pkgNameStr pkgNameStr.toLower
  | .math, .lean => mathLeanConfigFileContents pkgNameStr (escapeName! root)
  | .math, .toml => mathTomlConfigFileContents pkgNameStr root.toString

def createLeanActionWorkflow (dir : FilePath) : LogIO PUnit := do
  logVerbose "creating lean-action CI workflow"
  let workflowDir := dir / ".github" / "workflows"
  let workflowFile := workflowDir / "lean_action_ci.yml"
  if (← workflowFile.pathExists) then
    logVerbose "lean-action CI workflow already exists"
    return
  IO.FS.createDirAll workflowDir
  IO.FS.writeFile workflowFile leanActionWorkflowContents
  logVerbose s!"created lean-action CI workflow at '{workflowFile}'"

/-- Initialize a new Lake package in the given directory with the given name. -/
def initPkg (dir : FilePath) (name : Name) (tmp : InitTemplate) (lang : ConfigLang) (env : Lake.Env) : LogIO PUnit := do
  let configFile :=  dir / defaultConfigFile.addExtension lang.fileExtension
  if (← configFile.pathExists) then
    error "package already initialized"

  createLeanActionWorkflow dir
  -- determine the name to use for the root
  -- use upper camel case unless the specific module name already exists
  let (root, rootFile?) ← id do
    let root := name
    let rootFile := Lean.modToFilePath dir root "lean"
    if tmp = .exe || (← rootFile.pathExists) then
      return (root, some rootFile)
    else
      let root := toUpperCamelCase name
      let rootFile := Lean.modToFilePath dir root "lean"
      if (← rootFile.pathExists) then
        return (root, none)
      else
        return (root, rootFile)

  -- write template configuration file
  IO.FS.writeFile configFile <| tmp.configFileContents lang name root

  -- write example code if the files do not already exist
  if let some rootFile := rootFile? then
    let libDir := rootFile.withExtension ""
    let basicFile := libDir / "Basic.lean"
    unless (← basicFile.pathExists) do
      IO.FS.createDirAll libDir
      IO.FS.writeFile basicFile basicFileContents
    let rootContents := libRootFileContents root.toString root
    IO.FS.writeFile rootFile rootContents
  if tmp matches .std | .exe then
    let mainFile := dir / mainFileName
    unless (← mainFile.pathExists) do
      if tmp = .exe then
        IO.FS.writeFile mainFile <| exeFileContents
      else
        IO.FS.writeFile mainFile <| mainFileContents root

  -- Initialize a README.md file if none exists.
  let readmeFile := dir / "README.md"
  unless (← readmeFile.pathExists) do
    IO.FS.writeFile readmeFile (readmeFileContents <| dotlessName name)

  -- initialize a `.git` repository if none already
  let repo := GitRepo.mk dir
  unless (← repo.insideWorkTree) do
    try
      repo.quietInit
      unless upstreamBranch = "master" do
        repo.checkoutBranch upstreamBranch
    else
      logWarning "failed to initialize git repository"

  -- update `.gitignore` with additional entries for Lake
  let h ← IO.FS.Handle.mk (dir / ".gitignore") IO.FS.Mode.append
  h.putStr gitignoreContents

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
      logInfo "downloading mathlib `lean-toolchain` file"
      try
        download mathToolchainBlobUrl toolchainFile
      catch errPos =>
        logError "failed to download mathlib 'lean-toolchain' file; \
          you can manually copy it from:\n  {mathToolchainUrl}"
        throw errPos
    else
      IO.FS.writeFile toolchainFile <| env.toolchain ++ "\n"

def validatePkgName (pkgName : String) : LogIO PUnit := do
  if pkgName.isEmpty || pkgName.all (· == '.') || pkgName.any (· ∈ ['/', '\\']) then
    error s!"illegal package name '{pkgName}'"
  if pkgName.toLower ∈ ["init", "lean", "lake", "main"] then
    error "reserved package name"

def init (name : String) (tmp : InitTemplate) (lang : ConfigLang) (env : Lake.Env) (cwd : FilePath := ".") : LogIO PUnit := do
  let name ← id do
    if name == "." then
      let path ← IO.FS.realPath cwd
      match path.fileName with
      | some dirName => return dirName
      | none => error s!"illegal package name: could not derive one from '{path}'"
    else
      return name
  let name := name.trim
  validatePkgName name
  IO.FS.createDirAll cwd
  initPkg cwd (stringToLegalOrSimpleName name) tmp lang env

def new (name : String) (tmp : InitTemplate) (lang : ConfigLang)  (env : Lake.Env) (cwd : FilePath := ".") : LogIO PUnit := do
  let name := name.trim
  validatePkgName name
  let name := stringToLegalOrSimpleName name
  let dirName := dotlessName name
  let dir := cwd / dirName
  IO.FS.createDirAll dir
  initPkg dir name tmp lang env
