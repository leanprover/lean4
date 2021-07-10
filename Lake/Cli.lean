/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Lake.Init
import Lake.Build
import Lake.Help
import Lake.LeanConfig

namespace Lake
def getCwdPkg (args : List String) : IO Package := do
  let pkg ← Package.fromDir "." args
  if pkg.leanVersion ≠ leanVersionString then
    IO.eprintln $ "\nWARNING: Lean version mismatch: installed version is " ++
      leanVersionString ++ ", but package requires " ++ pkg.leanVersion ++ "\n"
  return pkg

def cli : (cmd : String) → (lakeArgs pkgArgs : List String) → IO Unit
| "init",         [name],   []      => init name
| "configure",    [],       pkgArgs => do configure (← getCwdPkg pkgArgs)
| "print-paths",  imports,  pkgArgs => do printPaths (← getCwdPkg pkgArgs) imports
| "build",        [],       pkgArgs => do build (← getCwdPkg pkgArgs)
| "build-lib",    [],       pkgArgs => do buildLib (← getCwdPkg pkgArgs)
| "build-bin",    [],       pkgArgs => do buildBin (← getCwdPkg pkgArgs)
| "help",         [cmd],    _       => IO.println <| help cmd
| _,              _,        _       => throw <| IO.userError usage

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
