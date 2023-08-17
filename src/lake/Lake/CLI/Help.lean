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
  --quiet, -q           hide progress messages
  --verbose, -v         show verbose information (command invocations)
  --lean=cmd            specify the `lean` command used by Lake
  -K key[=value]        set the configuration file option named key
  --old                 only rebuild modified modules (ignore transitive deps)
  --update, -U          update manifest before building

COMMANDS:
  new <name> <temp>     create a Lean package in a new directory
  init <name> <temp>    create a Lean package in the current directory
  build <targets>...    build targets
  update                update dependencies and save them to the manifest
  upload <tag>          upload build artifacts to a GitHub release
  clean                 remove build outputs
  script                manage and run workspace scripts
  scripts               shorthand for `lake script list`
  run <script>          shorthand for `lake script run`
  serve                 start the Lean language server
  env <cmd> <args>...   execute a command in Lake's environment
  exe <exe> <args>...   build an exe and run it in Lake's environment

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

LIBRARY FACETS:         build the library's ...
  lean (default)        Lean binaries (*.olean, *.ilean files)
  static                static binary (*.a file)
  shared                shared binary (*.so, *.dll, or *.dylib file)

MODULE FACETS:          build the module's ...
  deps                  transitive local imports & shared library dependencies
  bin (default)         Lean binaries (*.olean, *.ilean files) and *.c file
  o                     *.o object file (of its C file)
  dynlib                shared library (e.g., for `--load-dynlib`)

TARGET EXAMPLES:        build the ...
  a                     default facet of target `a`
  @a                    default target(s) of package `a`
  +A                    olean and .ilean files of module `A`
  a/b                   default facet of target `b` of package `a`
  a/+A:c                C file of module `A` of package `a`
  :foo                  facet `foo` of the root package

A bare `lake build` command will build the default facet of the root package.
Package dependencies are not updated during a build."

def helpUpdate :=
"Update dependencies and save them to the manifest

USAGE:
  lake update [<package>...]

Updates the Lake package manifest (i.e., `lake-manifest.json`),
downloading and upgrading packages as needed. For each new (transitive) git
dependency, the appropriate commit is cloned into a subdirectory of
`packagesDir`. No copy is made of local dependencies.

If a set of packages are specified, said dependencies are upgraded to
the latest version compatible with the package's configuration (or removed if
removed from the configuration). If there are dependencies on multiple versions
of the same package, the version materialized is undefined.

A bare `lake update` will upgrade all dependencies."

def helpUpload :=
"Upload build artifacts to a GitHub release

USAGE:
  lake upload <tag>

Packs the root package's `buildDir` into a `tar.gz` archive using `tar` and
then uploads the asset to the pre-existing GitHub release `tag` using `gh`."

def helpClean :=
"Remove build outputs

USAGE:
  lake clean [<package>...]

If no package is specified, deletes the build directories of every package in
the workspace. Otherwise, just deletes those of the specified packages."

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
  lake script run [[<package>/]<script>] [<args>...]

This command runs the given `script` from `package`, passing `args` to it.
Defaults to the root package.

A bare `lake run` command will run the default script(s) of the root package
(with no arguments)."

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
"Execute a command in Lake's environment

USAGE:
  lake env [<cmd>] [<args>...]

Spawns a new process executing `cmd` with the given `args` and with
the environment set based on the detected Lean/Lake installations and
the workspace configuration (if it exists).

Specifically, this command sets the following environment variables:

  LAKE                  set to the detected Lake executable
  LAKE_HOME             set to the detected Lake home
  LEAN_SYSROOT          set to the detected Lean toolchain directory
  LEAN_AR               set to the detected Lean `ar` binary
  LEAN_CC               set to the detected `cc` (if not using the bundled one)
  LEAN_PATH             adds Lake's and the workspace's Lean library dirs
  LEAN_SRC_PATH         adds Lake's and the workspace's source dirs
  PATH                  adds Lean's, Lake's, and the workspace's binary dirs
  PATH                  adds Lean's and the workspace's library dirs (Windows)
  DYLD_LIBRARY_PATH     adds Lean's and the workspace's library dirs (MacOS)
  LD_LIBRARY_PATH       adds Lean's and the workspace's library dirs (other)

A bare `lake env` will print out the variables set and their values,
using the form NAME=VALUE like the POSIX `env` command."

def helpExe :=
"Build an executable target and run it in Lake's environment

USAGE:
  lake exe <exe-target> [<args>...]

Looks for the executable target in the workspace (see `lake help build` to
learn how to specify targets), builds it if it is out of date, and then runs
it with the given `args` in Lake's environment (see `lake help env` for how
the environment is set up)."

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
| "upload"    => helpUpload
| "clean"     => helpClean
| "script"    => helpScriptCli
| "scripts"   => helpScriptList
| "run"       => helpScriptRun
| "serve"     => helpServe
| "env"       => helpEnv
| "exe"       => helpExe
| _           => usage
