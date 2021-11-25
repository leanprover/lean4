/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Lake.Version
import Lake.LeanVersion

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
  server                start the Lean language server
  run <script>          run arbitrary package scripts
  configure             download and build dependencies
  build [<targets>...]  configure and build targets
  clean                 remove build outputs

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

def helpRun :=
"Run arbitrary package scripts

USAGE:
  lake run <script> [-h] [-- <args>...]

This command runs the given script from the package configuration's
`scripts` field, passing `args` to it. If the given script does not exist,
errors and prints the list of available scripts.

You can pass -h/--help after the script name to print its docstring."

def helpServe :=
"Start the Lean language server

USAGE:
  lake serve [-- <args>...]

Run the language server of the Lean installation (i.e., via `lean --server`)
with the package configuration's `moreServerArgs` field and `args`.
"

def helpConfigure :=
"Download and build dependencies

USAGE:
  lake configure [-- <args>...]

This command sets up the directory with the package's dependencies
(i.e., by default, `lean_packages`). Passes `args` to the `Packager`
if specified.

For each (transitive) git dependency, the specified commit is checked out
into a sub-directory of `depsDir`. If there are dependencies on multiple
versions of the same package, the version materialized is undefined.
No copy is made of local dependencies."

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
Arguments to the `Packager` itself can be specified with `args`."

def helpClean :=
"Remove build outputs

USAGE:
  lake clean [-- <args>...]

Deletes the build directory of the package.
Arguments to the  `Packager` itself can be specified with `args`."

def helpCmd : (cmd : String) → String
| "new"       => helpNew
| "init"      => helpInit
| "run"       => helpRun
| "serve"     => helpServe
| "configure" => helpConfigure
| "build"     => helpBuild
| "clean"     => helpClean
| _           => usage

def help : (cmd? : Option String) → String
| some cmd => helpCmd cmd
| none => usage
