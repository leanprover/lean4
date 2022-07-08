/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Lake.Version

namespace Lake

def usage :=
uiVersionString ++ "

USAGE:
  lake [OPTIONS] <COMMAND>

OPTIONS:
  --version             print version and exit
  --help, -h            print help of the program or a command and exit
  --dir, -d=file        use the package configuration in a specific directory
  --file, -f=file       use a specific file for the package configuration
  --lean=cmd            specify the `lean` command used by Lake
  -K key[=value]        set the configuration file option named key

COMMANDS:
  new <name> [<temp>]   create a Lean package in a new directory
  init <name> [<temp>]  create a Lean package in the current directory
  build [<targets>...]  build targets
  update                update dependencies
  clean                 remove build outputs
  script                manage and run workspace scripts
  serve                 start the Lean language server
  env <cmd> [<args>...] execute a command in the workspace's environment

See `lake help <command>` for more information on a specific command."

def templateHelp :=
s!"The initial configuration and starter files are based on the template:

  std                   library and executable; default
  exe                   executable only
  lib                   library only
  math                  library only with a mathlib dependency"

def helpNew :=
s!"Create a Lean package in a new directory

USAGE:
  lake new <name> [<template>]

{templateHelp}"

def helpInit :=
s!"Create a Lean package in the current directory

USAGE:
  lake init <name> [<template>]

{templateHelp}"

def helpBuild :=
"Build targets

USAGE:
  lake build [<targets>...]

A target is specified with a string of the form:

  [[@]<package>/][<target>|[+]<module>][:<facet>]

The optional `@` and `+` markers can be used to disambiguate packages
and modules from other kinds of targets (i.e., executables and libraries).

PACKAGE FACETS:         build the package's ...
  exe                   binary executable
  leanLib               Lean library (*.olean and *.ilean files)
  staticLib             static library
  sharedLib             shared library

LIBRARY FACETS:         build the library's ...
  lean                  Lean binaries (*.olean and *.ilean files)
  static                static binary
  shared                shared binary

MODULE FACETS:          build the module's ...
  [default]             Lean binaries (*.olean and *.ilean files)
  c                     *.c file
  o                     *.o file (of the *.c file)
  dynlib                shared library (e.g., for `--load-dynlib`)

TARGET EXAMPLES:        build the ...
  a                     default facet of target `a`
  @a                    default target(s) of package `a`
  +A                    olean and .ilean files of module `A`
  a/b                   default facet of target `b` of package `a`
  a/+A:c                c file of module `A` of package `a`
  @a:leanLib            lean library of package `a`
  :exe                  root package's executable

A bare `build` command will build the default facet of the root package.
Package dependencies are not updated during a build."

def helpUpdate :=
"Update dependencies

USAGE:
  lake update

This command sets up the directory with the package's dependencies
(i.e., `packagesDir`, which is, by default, `lean_packages`).

For each (transitive) git dependency, the specified commit is checked out
into a sub-directory of `packagesDir`. Already checked out dependencies are
updated to the latest version compatible with the package's configuration.
If there are dependencies on multiple versions of the same package, the
version materialized is undefined. The specific revision of the resolved
packages are cached in the `manifest.json` file of the `packagesDir`.

No copy is made of local dependencies."

def helpClean :=
"Remove build outputs

USAGE:
  lake clean

Deletes the build directory of the package."

def helpScriptCli :=
"Manage Lake scripts

USAGE:
  lake script <COMMAND>

COMMANDS:
  list                  list available scripts
  run <script>          run a script
  doc <script>          print the docstring of a given script

See `lake help <command>` for more information on a specific command."

def helpScriptList :=
"List available scripts

USAGE:
  lake script list

This command prints the list of all available scripts in the workspace."

def helpScriptRun :=
"Run a script

USAGE:
  lake script run [<package>/]<script> [<args>...]

This command runs the given `script` from `package`, passing `args` to it.
Defaults to the root package."

def helpScriptDoc :=
"Print a script's docstring

USAGE:
  lake script doc [<package>/]<script>

Print the docstring of `script` in `package`. Defaults to the root package."

def helpServe :=
"Start the Lean language server

USAGE:
  lake serve [-- <args>...]

Run the language server of the Lean installation (i.e., via `lean --server`)
with the package configuration's `moreServerArgs` field and `args`.
"

def helpEnv :=
"Execute a command in the package's environment

USAGE:
  lake env <cmd> [<args>...]

Spawns a new process executing `cmd` with the given `args` and
with the `LEAN_PATH` environment variable set to include the `.olean`
directories of the package."

def helpScript : (cmd : String) → String
| "list"      => helpScriptList
| "run"       => helpScriptRun
| "doc"       => helpScriptDoc
| _           => helpScriptCli

def help : (cmd : String) → String
| "new"       => helpNew
| "init"      => helpInit
| "build"     => helpBuild
| "update"    => helpUpdate
| "clean"     => helpClean
| "script"    => helpScriptCli
| "serve"     => helpServe
| "env"       => helpEnv
| _           => usage
