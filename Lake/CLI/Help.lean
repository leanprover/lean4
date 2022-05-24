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

COMMANDS:
  new <name>            create a Lean package in a new directory
  init <name>           create a Lean package in the current directory
  build [<targets>...]  build targets
  update                update dependencies
  clean                 remove build outputs
  script                manage and run workspace scripts
  serve                 start the Lean language server
  env <cmd> [<args>...] execute a command in the workspace's environment

See `lake help <command>` for more information on a specific command."

def helpNew :=
"Create a Lean package in a new directory

USAGE:
  lake new <name>

This command creates a new Lean package with the given name in
a new directory with the same name."

def helpInit :=
"Create a Lean package in the current directory

USAGE:
  lake init <name>

This command creates a new Lean package with the given name in
the current directory."

def helpBuild :=
"Build targets

USAGE:
  lake build [<targets>...] [-- <args>...]

A target is specified with a string of the form '<package>/<module>:<facet>'.
The package must be the root package or one of its direct dependencies
(i.e., those listed in the root configuration file).

PACKAGE FACETS:
  bin                   build the package's binary
  staticLib             build the package's static library
  sharedLib             build the package's shared library
  oleans                build the package's *.olean files

MODULE FACETS:
  olean                 build the module's *.olean file
  c                     build the module's *.c file
  o                     build the module's *.o file

TARGET EXAMPLES:
  a                     build the default facet of package `a`
  a/A                   build the .olean file of module `A` of package `a`
  a/A:c                 build the .c file of module `A` of package `a`
  a:oleans              build the olean files of package `a`
  :bin                  build the root package's binary

A bare `build` command will build the default facet of the root package.
Arguments to the `Packager` itself can be specified with `args`.
Package dependencies are not updated during a build."

def helpUpdate :=
"Update dependencies

USAGE:
  lake update [-- <args>...]

This command sets up the directory with the package's dependencies
(i.e., `packagesDir` which is, by default, `lean_packages`).
Passes `args` to the `Packager` if specified.

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
  lake clean [-- <args>...]

Deletes the build directory of the package.
Arguments to the  `Packager` itself can be specified with `args`."

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
