/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
module

prelude
public import Lake.Config.Env
public import Lake.Config.Lang
import Lake.Util.Git
import Lake.Load.Workspace
import Init.Data.String.Modify

namespace Lake
open Git System
open Lean (Name)

/-- The default module of an executable in `std` package. -/
public def defaultExeRoot : Name := `Main

def gitignoreContents :=
s!"/{defaultLakeDir}
"

def basicFileContents :=
s!"def hello := \"world\"
"

def libRootFileContents (libName : String) (libRoot : Name) :=
s!"-- This module serves as the root of the `{libName}` library.
-- Import modules here that should be built as part of the library.
import {libRoot}.Basic
"

def mathLibRootFileContents (libRoot : Name) :=
s!"import {libRoot}.Basic
"

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

def mathLaxLeanConfigFileContents (pkgName libRoot rev : String) :=
s!"import Lake
open Lake DSL

package {repr pkgName} where
  version := v!\"0.1.0\"
  keywords := #[\"math\"]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]

require \"leanprover-community\" / \"mathlib\" @ git {repr rev}

@[default_target]
lean_lib {libRoot} where
  -- add any library configuration options here
"

def mathLaxTomlConfigFileContents (pkgName libRoot rev : String) :=
s!"name = {repr pkgName}
version = \"0.1.0\"
keywords = [\"math\"]
defaultTargets = [{repr libRoot}]

[leanOptions]
pp.unicode.fun = true # pretty-prints `fun a ↦ b`

[[require]]
name = \"mathlib\"
scope = \"leanprover-community\"
rev = {repr rev}

[[lean_lib]]
name = {repr libRoot}
"

def mathLeanConfigFileContents (pkgName libRoot rev : String) :=
s!"import Lake
open Lake DSL

package {repr pkgName} where
  version := v!\"0.1.0\"
  keywords := #[\"math\"]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`maxSynthPendingDepth, .ofNat 3⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩,
  ]

require \"leanprover-community\" / \"mathlib\" @ git {repr rev}

@[default_target]
lean_lib {libRoot} where
  -- add any library configuration options here
"

def mathTomlConfigFileContents (pkgName libRoot rev : String) :=
s!"name = {repr pkgName}
version = \"0.1.0\"
keywords = [\"math\"]
defaultTargets = [{repr libRoot}]

[leanOptions]
pp.unicode.fun = true # pretty-prints `fun a ↦ b`
relaxedAutoImplicit = false
weak.linter.mathlibStandardSet = true
maxSynthPendingDepth = 3

[[require]]
name = \"mathlib\"
scope = \"leanprover-community\"
rev = {repr rev}

[[lean_lib]]
name = {repr libRoot}
"

def readmeFileContents (pkgName : String) := s!"# {pkgName}"

def mathReadmeFileContents (pkgName : String) := s!"# {pkgName}

## GitHub configuration

To set up your new GitHub repository, follow these steps:

* Under your repository name, click **Settings**.
* In the **Actions** section of the sidebar, click \"General\".
* Check the box **Allow GitHub Actions to create and approve pull requests**.
* Click the **Pages** section of the settings sidebar.
* In the **Source** dropdown menu, select \"GitHub Actions\".

After following the steps above, you can remove this section from the README file.
"

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
      - uses: actions/checkout@v5
      - uses: leanprover/lean-action@v1
"

def mathBuildActionWorkflowContents :=
"name: Lean Action CI

on:
  push:
  pull_request:
  workflow_dispatch:

# Sets permissions of the GITHUB_TOKEN to allow deployment to GitHub Pages
permissions:
  contents: read # Read access to repository contents
  pages: write # Write access to GitHub Pages
  id-token: write # Write access to ID tokens

jobs:
  build:
    runs-on: ubuntu-latest

    steps:
      - uses: actions/checkout@v5
      - uses: leanprover/lean-action@v1
      - uses: leanprover-community/docgen-action@v1
"

def mathUpdateActionWorkflowContents :=
"name: Update Dependencies

on:
  # schedule:             # Sets a schedule to trigger the workflow
  #   - cron: \"0 8 * * *\" # Every day at 08:00 AM UTC (see https://docs.github.com/en/actions/writing-workflows/choosing-when-your-workflow-runs/events-that-trigger-workflows#schedule)
  workflow_dispatch:    # Allows the workflow to be triggered manually via the GitHub interface

jobs:
  check-for-updates: # Determines which updates to apply.
    runs-on: ubuntu-latest
    outputs:
      is-update-available: ${{ steps.check-for-updates.outputs.is-update-available }}
      new-tags: ${{ steps.check-for-updates.outputs.new-tags }}
    steps:
      - name: Run the action
        id: check-for-updates
        uses: leanprover-community/mathlib-update-action@v1
        # START CONFIGURATION BLOCK 1
        # END CONFIGURATION BLOCK 1
  do-update: # Runs the upgrade, tests it, and makes a PR/issue/commit.
    runs-on: ubuntu-latest
    permissions:
      contents: write      # Grants permission to push changes to the repository
      issues: write        # Grants permission to create or update issues
      pull-requests: write # Grants permission to create or update pull requests
    needs: check-for-updates
    if: ${{ needs.check-for-updates.outputs.is-update-available == 'true' }}
    strategy: # Runs for each update discovered by the `check-for-updates` job.
      max-parallel: 1 # Ensures that the PRs/issues are created in order.
      matrix:
        tag: ${{ fromJSON(needs.check-for-updates.outputs.new-tags) }}
    steps:
      - name: Run the action
        id: update-the-repo
        uses: leanprover-community/mathlib-update-action/do-update@v1
        with:
          tag: ${{ matrix.tag }}
          # START CONFIGURATION BLOCK 2
          on_update_succeeds: pr # Create a pull request if the update succeeds
          on_update_fails: issue # Create an issue if the update fails
          # END CONFIGURATION BLOCK 2
"

def createReleaseActionWorkflowContents :=
"name: Create Release

on:
  push:
    branches:
      - 'main'
      - 'master'
    paths:
      - 'lean-toolchain'

jobs:
  lean-release-tag:
    name: Add Lean release tag
    runs-on: ubuntu-latest
    permissions:
      contents: write
    steps:
    - name: lean-release-tag action
      uses: leanprover-community/lean-release-tag@v1
      with:
        do-release: true
        GITHUB_TOKEN: ${{ secrets.GITHUB_TOKEN }}
"

/-- Lake package template identifier. -/
public inductive InitTemplate
| std | exe | lib | mathLax | math
deriving Repr, DecidableEq

public instance : Inhabited InitTemplate := ⟨.std⟩

public def InitTemplate.ofString? : String → Option InitTemplate
| "std" => some .std
| "exe" => some .exe
| "lib" => some .lib
| "math-lax" => some .mathLax
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

def InitTemplate.configFileContents
  (tmp : InitTemplate) (lang : ConfigLang) (pkgName : Name) (root : Name)
  (leanVer? : Option LeanVer)
: String :=
  let pkgNameStr := dotlessName pkgName
  let mathRev := leanVer?.elim "master" (s!"v{·.toString}")
  match tmp, lang with
  | .std, .lean => stdLeanConfigFileContents pkgNameStr (escapeName! root) pkgNameStr.toLower
  | .std, .toml => stdTomlConfigFileContents pkgNameStr root.toString pkgNameStr.toLower
  | .lib, .lean => libLeanConfigFileContents pkgNameStr (escapeName! root)
  | .lib, .toml => libTomlConfigFileContents pkgNameStr root.toString
  | .exe, .lean => exeLeanConfigFileContents pkgNameStr pkgNameStr.toLower
  | .exe, .toml => exeTomlConfigFileContents pkgNameStr pkgNameStr.toLower
  | .mathLax, .lean => mathLaxLeanConfigFileContents pkgNameStr (escapeName! root) mathRev
  | .mathLax, .toml => mathLaxTomlConfigFileContents pkgNameStr root.toString mathRev
  | .math, .lean => mathLeanConfigFileContents pkgNameStr (escapeName! root) mathRev
  | .math, .toml => mathTomlConfigFileContents pkgNameStr root.toString mathRev

def createLeanActionWorkflow (dir : FilePath) (tmp : InitTemplate) : LogIO PUnit := do
  logVerbose "creating lean-action CI workflow"
  let workflowDir := dir / ".github" / "workflows"
  IO.FS.createDirAll workflowDir

  let workflowFile := workflowDir / "lean_action_ci.yml"
  if (← workflowFile.pathExists) then
    logVerbose "lean-action CI workflow already exists"
    return
  if tmp = .math then
    IO.FS.writeFile workflowFile mathBuildActionWorkflowContents
  else
    IO.FS.writeFile workflowFile leanActionWorkflowContents
  logVerbose s!"created lean-action CI workflow at '{workflowFile}'"

  if tmp = .math then
    -- A workflow for automatically creating update PRs/issues.
    let workflowFile := workflowDir / "update.yml"
    if (← workflowFile.pathExists) then
      logVerbose "Mathlib update CI workflow already exists"
      return
    IO.FS.writeFile workflowFile mathUpdateActionWorkflowContents
    logVerbose s!"created Mathlib update CI workflow at '{workflowFile}'"
    -- A workflow for tagging commits that bump the Lean toolchain version.
    let workflowFile := workflowDir / "create-release.yml"
    if (← workflowFile.pathExists) then
      logVerbose "create-release CI workflow already exists"
      return
    IO.FS.writeFile workflowFile createReleaseActionWorkflowContents
    logVerbose s!"created create-release CI workflow at '{workflowFile}'"

/-- Initialize a new Lake package in the given directory with the given name. -/
def initPkg
  (dir : FilePath) (name : Name) (tmp : InitTemplate) (lang : ConfigLang)
  (env : Lake.Env) (offline := false)
: LoggerIO PUnit := do
  let configFile :=  dir / defaultConfigFile.addExtension lang.fileExtension
  if (← configFile.pathExists) then
    error "package already initialized"

  createLeanActionWorkflow dir tmp
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

  -- Compute the Lean version from the environment toolchain
  let leanVer? := match ToolchainVer.ofString env.toolchain with
    | .release ver => some ver
    | _ => none

  -- write template configuration file
  IO.FS.writeFile configFile <| tmp.configFileContents lang name root leanVer?

  -- write example code if the files do not already exist
  if let some rootFile := rootFile? then
    let libDir := rootFile.withExtension ""
    let basicFile := libDir / "Basic.lean"
    unless (← basicFile.pathExists) do
      IO.FS.createDirAll libDir
      IO.FS.writeFile basicFile basicFileContents
    let rootContents := if tmp = .math then
      mathLibRootFileContents root
    else
      libRootFileContents root.toString root
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
    let contents := if tmp = .math then
        mathReadmeFileContents <| dotlessName name
      else
        readmeFileContents <| dotlessName name
    IO.FS.writeFile readmeFile contents

  -- initialize a `.git` repository if none already
  let repo := GitRepo.mk dir
  unless (← repo.insideWorkTree) do
    try
      repo.quietInit
      unless upstreamBranch = "master" do
        repo.checkoutBranch upstreamBranch
    catch _ =>
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
          logWarning "could not create a `lean-toolchain` file for the new package; \
            no known toolchain name for the current Elan/Lean/Lake"
    else
      IO.FS.writeFile toolchainFile <| env.toolchain ++ "\n"
  if tmp matches .mathLax | .math then
    if leanVer?.isNone then
      logWarning "creating a new math package with a non-release Lean toolchain; \
        Mathlib may not work properly"
    unless offline do
      -- Checkout mathlib and pin the version in the manifest
      updateManifest { lakeEnv := env, wsDir := dir, updateToolchain := false }

def validatePkgName (pkgName : String) : LogIO PUnit := do
  if pkgName.isEmpty || pkgName.all (· == '.') || pkgName.any (· ∈ ['/', '\\']) then
    error s!"illegal package name '{pkgName}'"
  if pkgName.toLower ∈ ["init", "lean", "lake", "main"] then
    error "reserved package name"

public def init
  (name : String) (tmp : InitTemplate) (lang : ConfigLang)
  (env : Lake.Env) (cwd : FilePath := ".") (offline := false)
: LoggerIO PUnit := do
  let name ← id do
    if name == "." then
      let path ← IO.FS.realPath cwd
      match path.fileName with
      | some dirName => return dirName
      | none => error s!"illegal package name: could not derive one from '{path}'"
    else
      return name
  let name := name.trimAscii.copy
  validatePkgName name
  IO.FS.createDirAll cwd
  initPkg cwd (stringToLegalOrSimpleName name) tmp lang env offline

public def new
  (name : String) (tmp : InitTemplate) (lang : ConfigLang)
  (env : Lake.Env) (cwd : FilePath := ".") (offline := false)
: LoggerIO PUnit := do
  let name := name.trimAscii.copy
  validatePkgName name
  let name := stringToLegalOrSimpleName name
  let dirName := dotlessName name
  let dir := cwd / dirName
  IO.FS.createDirAll dir
  initPkg dir name tmp lang env offline
