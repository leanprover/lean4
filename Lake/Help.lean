/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Lake.Version
import Lake.LeanVersion

namespace Lake

def usage :=
s!"Lake version {versionString} (Lean version {uiLeanVersionString})

Usage:
  lake <command>

new <name>       create a Lean package in a new directory
init <name>      create a Lean package in the current directory
run <script>     run arbitrary package scripts
configure        download and build dependencies
build            configure and build *.olean files
build-lib        configure and build a static library
build-bin        configure and build a native binary executable
clean            remove build outputs

See `lake help <command>` for more information on a specific command."

def helpNew :=
"Create a Lean package in a new directory

Usage:
  lake new <name>

This command creates a new Lean package with the given name in
a new directory with the same name."

def helpInit :=
"Create a Lean package in the current directory

Usage:
  lake init <name>

This command creates a new Lean package with the given name in
the current directory."

def helpRun :=
"Run arbitrary package scripts

Usage:
  lake run <script> [-- <args>...]

This command runs the given script from the package configuration's
`scripts` field, passing `args` to it. If the given script does not exist,
it will list the available scripts."

def helpConfigure :=
"Download and build dependencies

Usage:
  lake configure [-- <args>...]

This command sets up the directory with the package's dependencies
(i.e., by default, `lean_packages`). Passes `args` to the `Packager`
if specified.

For each (transitive) git dependency, the specified commit is checked out
into a sub-directory of `depsDir`. If there are dependencies on multiple
versions of the same package, the version materialized is undefined.
No copy is made of local dependencies."

def helpBuild :=
"Configure this package and build *.olean files

Usage:
  lake build [-- <args>...]

This command configures the package's dependencies and then builds the package
with `lean`. Additional arguments can be passed to `lean` by setting the
`leanArgs` field in the package's configuration. Arguments to the `Packager`
itself can be specified with `args`."

def helpBuildLib :=
"Configure this package and build a static library

Usage:
  lake build-lib [-- <args>...]

This command configures this package's dependencies, builds the package,
compiles the extracted C code with `leanc`, and uses `ar` to produce a static
library.

Additional arguments can be passed to `lean` or `leanc` by setting the
`leanArgs` or `leancArgs` fields in the package's configuration. Arguments
to the `Packager` itself can be specified with `args`."

def helpBuildBin :=
"Configure the package and build a native binary executable

Usage:
  lake build-bin [-- <args>...]

This command configures this package's dependencies, builds the package,
compiles the extracted C code `leanc`, and then links the results together
with `leanc` to produce a native binary executable.

This requires a declaration of name `main` in the root namespace, which must
return `IO Unit` or `IO UInt32` (the exit code) and may accept the program's
command line arguments as a `List String` parameter.

Additional  arguments can be passed to `lean`, the  `leanc` compiler, or the
`leanc` linker by setting the `leanArgs`, `leancArgs`, or `linkArgs` fields in
the package's configuration. Arguments to the  `Packager` itself can be
specified with `args`."

def helpClean :=
"Remove build outputs

Usage:
  lake clean [-- <args>...]

Deletes the build directory of the package.
Arguments to the  `Packager` itself can be specified with `args`."

def help : (cmd : String) → String
| "new"       => helpNew
| "init"      => helpInit
| "run"       => helpRun
| "configure" => helpConfigure
| "build"     => helpBuild
| "build-lib" => helpBuildLib
| "build-bin" => helpBuildBin
| "clean"     => helpClean
| _           => usage
