/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich
-/
import Leanpkg.Resolve
import Leanpkg.Git

namespace Leanpkg

def readManifest : IO Manifest := do
  let m ← Manifest.fromFile leanpkgTomlFn
  if m.leanVersion ≠ leanVersionString then
    IO.eprintln $ "\nWARNING: Lean version mismatch: installed version is " ++ leanVersionString
       ++ ", but package requires " ++ m.leanVersion ++ "\n"
  return m

def writeManifest (manifest : Lean.Syntax) (fn : String) : IO Unit := do
  IO.FS.writeFile fn manifest.reprint.get!

def configure : IO String := do
  let d ← readManifest
  IO.eprintln $ "configuring " ++ d.name ++ " " ++ d.version
  let assg ← solveDeps d
  let paths ← constructPath assg
  for path in paths do
    unless path == "./." do
      -- TODO: share build of common dependencies
      execCmd {
        cmd := "leanpkg"
        cwd := path
        args := #["build"]
      }
  System.FilePath.searchPathSeparator.toString.intercalate <| paths.map (· ++ "/build")

def build (leanArgs : List String) : IO Unit := do
  let manifest ← readManifest
  let path ← configure
  let leanArgs := (match manifest.timeout with | some t => ["-T", toString t] | none => []) ++ leanArgs
  let mut spawnArgs := {
    cmd := "leanmake"
    cwd := manifest.effectivePath
    args := #[s!"LEAN_OPTS={" ".intercalate leanArgs}", s!"LEAN_PATH={path}"]
  }
  if System.Platform.isWindows then
    spawnArgs := { spawnArgs with cmd := "sh", args := #[s!"{← IO.appDir}\\{spawnArgs.cmd}"] ++ spawnArgs.args }
  execCmd spawnArgs

def initGitignoreContents :=
  "/build
"

def initPkg (n : String) (fromNew : Bool) : IO Unit := do
  IO.FS.writeFile leanpkgTomlFn s!"[package]
name = \"{n}\"
version = \"0.1\"
"
  IO.FS.writeFile s!"{n.capitalize}.lean" "def main : IO Unit :=
  IO.println \"Hello, world!\"
"
  let h ← IO.FS.Handle.mk ".gitignore" IO.FS.Mode.append (bin := false)
  h.putStr initGitignoreContents
  let gitEx ← IO.isDir ".git"
  unless gitEx do
    (do
      execCmd {cmd := "git", args := #["init", "-q"]}
      unless upstreamGitBranch = "master" do
        execCmd {cmd := "git", args := #["checkout", "-B", upstreamGitBranch]}
    ) <|> IO.println "WARNING: failed to initialize git repository"

def init (n : String) := initPkg n false

def usage :=
  "Lean package manager, version " ++ uiLeanVersionString ++ "

Usage: leanpkg <command>

configure              download dependencies
build [-- <Lean-args>] download dependencies and build *.olean files
init <name>            create a Lean package in the current directory

See `leanpkg help <command>` for more information on a specific command."

def main : (cmd : String) → (leanpkgArgs leanArgs : List String) → IO Unit
  | "configure", [],     []        => discard <| configure
  | "build",     _,      leanArgs  => build leanArgs
  | "init",      [Name], []        => init Name
  | "help",      ["configure"], [] => IO.println "Download dependencies

Usage:
  leanpkg configure

This command sets up the `build/deps` directory.

For each (transitive) git dependency, the specified commit is checked out
into a sub-directory of `build/deps`. If there are dependencies on multiple
versions of the same package, the version materialized is undefined. No copy
is made of local dependencies."
  | "help",       ["build"], []    => IO.println "download dependencies and build *.olean files

Usage:
  leanpkg build [-- <lean-args>]

This command invokes `Leanpkg configure` followed by
`Leanmake <lean-args>`, building the package's Lean files as well as
(transitively) imported files of dependencies. If defined, the `package.timeout`
configuration value is passed to Lean via its `-T` parameter."
  | "help",       ["init"], []     => IO.println "Create a new Lean package in the current directory

Usage:
  leanpkg init <name>

This command creates a new Lean package with the given name in the current
directory."
  | "help",       _,     []        => IO.println usage
  | _,            _,     _         => throw <| IO.userError usage

private def splitCmdlineArgsCore : List String → List String × List String
  | []           => ([], [])
  | (arg::args)  => if arg == "--"
                    then ([], args)
                    else
                      let (outerArgs, innerArgs) := splitCmdlineArgsCore args
                      (arg::outerArgs, innerArgs)

def splitCmdlineArgs : List String → IO (String × List String × List String)
| [] => throw <| IO.userError usage
| [cmd] => return (cmd, [], [])
| (cmd::rest) =>
  let (outerArgs, innerArgs) := splitCmdlineArgsCore rest
  return (cmd, outerArgs, innerArgs)

end Leanpkg

def main (args : List String) : IO Unit := do
  Lean.initSearchPath none  -- HACK
  let (cmd, outerArgs, innerArgs) ← Leanpkg.splitCmdlineArgs args
  Leanpkg.main cmd outerArgs innerArgs
