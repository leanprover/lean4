/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Lake.Version

namespace Lake

def usage :=
"Lake, version " ++ versionString ++ "

Usage:
  lake <command>

init <name>      create a Lean package in the current directory
configure        download and build dependencies
build            configure and build *.olean files
build-lib        configure and build a static library
build-bin        configure and build a native binary executable

See `lake help <command>` for more information on a specific command."

def helpConfigure :=
"Download and build dependencies

Usage:
  lake configure

This command sets up the `build/deps` directory.

For each (transitive) git dependency, the specified commit is checked out
into a sub-directory of `build/deps`. If there are dependencies on multiple
versions of the same package, the version materialized is undefined. No copy
is made of local dependencies."

def helpBuild :=
"Configure this package and build *.olean files

Usage:
  lake build

This command configures the package's dependencies and then builds the package
with `lean`. Additional arguments can be passed to `lean` by setting the
`leanArgs` field in the package's configuration."

def helpBuildLib :=
"Configure this package and build a static library

Usage:
  lake build-lib

This command configures this package's dependencies, builds the package itself,
compiles the extracted C code with `leanc`, and uses `ar` to produce a static
library in  `build/lib`.

Additional arguments can be passed to `lean` or `leanc` by setting the
`leanArgs` or `leancArgs` fields in the package's configuration."

def helpBuildBin :=
"Configure the package and build a native binary executable

Usage:
  lake build-bin

This command configures this package's dependencies, builds the package itself,
compiles the extracted C code `leannc`, and then links the object files with
`leanc` to produce a native binary executable in `build/bin`.

This requires a declaration of name `main` in the root namespace, which must
return `IO Unit` or `IO UInt32` (the exit code) and may accept the program's
command line arguments as a `List String` parameter.

Additional  arguments can be passed to `lean`, the  `leanc` compiler, or the
`leanc` linker by setting the `leanArgs`, `leancArgs`, or `linkArgs` fields in
the package's configuration."

def helpInit :=
"Create a new Lean package in the current directory

Usage:
  lake init <name>

This command creates a new Lean package with the given name in the current
directory."

def help : (cmd : String) → String
| "init"      => helpInit
| "configure" => helpConfigure
| "build"     => helpBuild
| "build-lib" => helpBuildLib
| "build-bin" => helpBuildBin
| _           => usage
