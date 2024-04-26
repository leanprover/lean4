/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Lake.Util.Git
import Lake.Util.Sugar
import Lake.Config.Lang
import Lake.Config.Package
import Lake.Config.Workspace
import Lake.Load.Config
import Lake.Build.Actions

namespace Lake
open Git System

/-- The default module of an executable in `std` package. -/
def defaultExeRoot : Name := `Main

/-- `elan` toolchain file name -/
def toolchainFileName : FilePath := "lean-toolchain"

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

def stdLeanConfigFileContents (pkgName libRoot exeName : String) :=
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

def stdTomlConfigFileContents (pkgName libRoot exeName : String) :=
s!"name = {repr pkgName}
defaultTargets = [{repr exeName}]

[[lean_lib]]
name = {repr libRoot}

[[lean_exe]]
name = {repr exeName}
root = \"Main\"
"

def exeLeanConfigFileContents (pkgName exeRoot : String) :=
s!"import Lake
open Lake DSL

package {pkgName} where
  -- add package configuration options here

@[default_target]
lean_exe {exeRoot} where
  -- add executable configuration options here
"

def exeTomlConfigFileContents (pkgName exeRoot : String) :=
s!"name = {repr pkgName}
defaultTargets = [{repr exeRoot}]

[[lean_exe]]
name = {repr exeRoot}
"

def libLeanConfigFileContents (pkgName libRoot : String) :=
s!"import Lake
open Lake DSL

package {pkgName} where
  -- add package configuration options here

@[default_target]
lean_lib {libRoot} where
  -- add library configuration options here
"

def libTomlConfigFileContents (pkgName libRoot : String) :=
s!"name = {repr pkgName}
defaultTargets = [{repr libRoot}]

[[lean_lib]]
name = {repr libRoot}
"

def mathLeanConfigFileContents (pkgName libRoot : String) :=
s!"import Lake
open Lake DSL

package {pkgName} where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require mathlib from git
  \"https://github.com/leanprover-community/mathlib4.git\"

@[default_target]
lean_lib {libRoot} where
  -- add any library configuration options here
"

def mathTomlConfigFileContents (pkgName libRoot : String) :=
s!"name = {repr pkgName}
defaultTargets = [{repr libRoot}]

[leanOptions]
pp.unicode.fun = true # pretty-prints `fun a ↦ b`

[[require]]
name = \"mathlib\"
git = \"https://github.com/leanprover-community/mathlib4.git\"

[[lean_lib]]
name = {repr libRoot}
"

def mathToolchainUrl : String :=
  "https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain"

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

def InitTemplate.configFileContents  (tmp : InitTemplate) (lang : ConfigLang) (pkgName : Name) (root : Name) : String :=
  match tmp, lang with
  | .std, .lean => stdLeanConfigFileContents (escapeName! pkgName) (escapeName! root)
    (escapeIdent <| pkgName.toStringWithSep "-" false).toLower
  | .std, .toml => stdTomlConfigFileContents pkgName.toString root.toString
    (pkgName.toStringWithSep "-" false).toLower
  | .lib, .lean => libLeanConfigFileContents (escapeName! pkgName) (escapeName! root)
  | .lib, .toml => libTomlConfigFileContents pkgName.toString root.toString
  | .exe, .lean => exeLeanConfigFileContents (escapeName! pkgName) (escapeName! root)
  | .exe, .toml => exeTomlConfigFileContents pkgName.toString root.toString
  | .math, .lean => mathLeanConfigFileContents (escapeName! pkgName) (escapeName! root)
  | .math, .toml => mathTomlConfigFileContents pkgName.toString root.toString

/-- Initialize a new Lake package in the given directory with the given name. -/
def initPkg (dir : FilePath) (name : String) (tmp : InitTemplate) (lang : ConfigLang) (env : Lake.Env) : LogIO PUnit := do
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
  let configFile :=  dir / match lang with
    | .lean => defaultLeanConfigFile | .toml => defaultTomlConfigFile
  if (← configFile.pathExists) then
    error  "package already initialized"
  let contents := tmp.configFileContents lang pkgName root
  IO.FS.writeFile configFile contents

  -- write example code if the files do not already exist
  let rootNameStr := escapeName! root
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
      repo.checkoutBranch "master"
    else
      logWarning "failed to initialize git repository"

def validatePkgName (pkgName : String) : LogIO PUnit := do
  if pkgName.isEmpty || pkgName.all (· == '.') || pkgName.any (· ∈ ['/', '\\']) then
    error s!"illegal package name '{pkgName}'"
  if pkgName.toLower ∈ ["init", "lean", "lake", "main"] then
    error "reserved package name"

def init (pkgName : String) (tmp : InitTemplate) (lang : ConfigLang) (env : Lake.Env) (cwd : FilePath := ".") : LogIO PUnit := do
  let pkgName ← do
    if pkgName == "." then
      let path ← IO.FS.realPath cwd
      match path.fileName with
      | some dirName => pure dirName
      | none => error s!"illegal package name: could not derive one from '{path}'"
    else
      pure pkgName
  let pkgName := pkgName.trim
  validatePkgName pkgName
  IO.FS.createDirAll cwd
  initPkg cwd pkgName tmp lang env

def new (pkgName : String) (tmp : InitTemplate) (lang : ConfigLang)  (env : Lake.Env) (cwd : FilePath := ".") : LogIO PUnit := do
  let pkgName := pkgName.trim
  validatePkgName pkgName
  let dirName := cwd / pkgName.map fun chr => if chr == '.' then '-' else chr
  IO.FS.createDirAll dirName
  initPkg dirName pkgName tmp lang env
