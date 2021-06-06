/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Leanpkg2.Init
import Leanpkg2.Build
import Leanpkg2.TomlConfig

namespace Leanpkg2

def usage :=
"Lean package manager, version " ++ uiLeanVersionString ++ "
Usage: leanpkg <command>

init <name>      create a Lean package in the current directory
configure        download and build dependencies
build [<args>]   configure and build *.olean files

See `leanpkg help <command>` for more information on a specific command."

def helpConfigure :=
"Download dependencies

Usage:
  leanpkg configure

This command sets up the `build/deps` directory.

For each (transitive) git dependency, the specified commit is checked out
into a sub-directory of `build/deps`. If there are dependencies on multiple
versions of the same package, the version materialized is undefined. No copy
is made of local dependencies."

def helpBuild :=
"Download dependencies and build *.olean files

Usage:
  leanpkg build [<leanmake-args>] [-- <lean-args>]

This command invokes `leanpkg configure` followed by `leanmake <leanmake-args> LEAN_OPTS=<lean-args>`.
If defined, the `package.timeout` configuration value is passed to Lean via its `-T` parameter.
If no <lean-args> are given, only .olean files will be produced in `build/`. If `lib` or `bin`
is passed instead, the extracted C code is compiled with `c++` and a static library in `build/lib`
or an executable in `build/bin`, respectively, is created. `leanpkg build bin` requires a declaration
of name `main` in the root namespace, which must return `IO Unit` or `IO UInt32` (the exit code) and
may accept the program's command line arguments as a `List String` parameter.

NOTE: building and linking dependent libraries currently has to be done manually, e.g.
```
$ (cd a; leanpkg build lib)
$ (cd b; leanpkg build bin LINK_OPTS=../a/build/lib/libA.a)
```"

def helpInit :=
"Create a new Lean package in the current directory

Usage:
  leanpkg init <name>

This command creates a new Lean package with the given name in the current
directory."

def getRootPkg : IO Package := do
  let cfg ← PackageConfig.fromTomlFile leanpkgToml
  if cfg.leanVersion ≠ leanVersionString then
    IO.eprintln $ "\nWARNING: Lean version mismatch: installed version is " ++
      leanVersionString ++ ", but package requires " ++ cfg.leanVersion ++ "\n"
  return ⟨".", cfg⟩

def cli : (cmd : String) → (leanpkgArgs leanArgs : List String) → IO Unit
| "init",         [name],         []        => init name
| "configure",    [],             []        => do configure (← getRootPkg)
| "print-paths",  imports,        leanArgs  => do printPaths (← getRootPkg) imports leanArgs
| "build",        makeArgs,       leanArgs  => do build (← getRootPkg) makeArgs leanArgs
| "help",         ["init"],       []        => IO.println helpInit
| "help",         ["configure"],  []        => IO.println helpConfigure
| "help",         ["build"],      []        => IO.println helpBuild
| "help",         _,              []        => IO.println usage
| _,              _,              _         => throw <| IO.userError usage

private def splitCmdlineArgsCore : List String → List String × List String
| [] => ([], [])
| (arg::args) =>
  if arg == "--" then
    ([], args)
  else
    let (outerArgs, innerArgs) := splitCmdlineArgsCore args
    (arg::outerArgs, innerArgs)

def splitCmdlineArgs : List String → IO (String × List String × List String)
| [] => throw <| IO.userError usage
| [cmd] => return (cmd, [], [])
| (cmd::rest) =>
  let (outerArgs, innerArgs) := splitCmdlineArgsCore rest
  return (cmd, outerArgs, innerArgs)
