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

COMMANDS:
  new <name> <temp>     create a Lean package in a new directory
  init <name> <temp>    create a Lean package in the current directory
  build <targets>...    build targets
  exe <exe> <args>...   build an exe and run it in Lake's environment
  check-build           check if any default build targets are configured
  test                  test the package using the configured test driver
  check-test            check if there is a properly configured test driver
  lint                  lint the package using the configured lint driver
  check-lint            check if there is a properly configured lint driver
  clean                 remove build outputs
  env <cmd> <args>...   execute a command in Lake's environment
  lean <file>           elaborate a Lean file in Lake's context
  update                update dependencies and save them to the manifest
  pack                  pack build artifacts into an archive for distribution
  unpack                unpack build artifacts from an distributed archive
  upload <tag>          upload build artifacts to a GitHub release
  script                manage and run workspace scripts
  scripts               shorthand for `lake script list`
  run <script>          shorthand for `lake script run`
  translate-config      change language of the package configuration
  serve                 start the Lean language server

BASIC OPTIONS:
  --version             print version and exit
  --help, -h            print help of the program or a command and exit
  --dir, -d=file        use the package configuration in a specific directory
  --file, -f=file       use a specific file for the package configuration
  -K key[=value]        set the configuration file option named key
  --old                 only rebuild modified modules (ignore transitive deps)
  --rehash, -H          hash all files for traces (do not trust `.hash` files)
  --update, -U          update dependencies on load (e.g., before a build)
  --reconfigure, -R     elaborate configuration files instead of using OLeans
  --keep-toolchain      do not update toolchain on workspace update
  --no-build            exit immediately if a build target is not up-to-date
  --no-cache            build packages locally; do not download build caches
  --try-cache           attempt to download build caches for supported packages

OUTPUT OPTIONS:
  --quiet, -q           hide informational logs and the progress indicator
  --verbose, -v         show trace logs (command invocations) and built targets
  --ansi, --no-ansi     toggle the use of ANSI escape codes to prettify output
  --log-level=lv        minimum log level to output on success
                        (levels: trace, info, warning, error)
  --fail-level=lv       minimum log level to fail a build (default: error)
  --iofail              fail build if any I/O or other info is logged
                        (same as --fail-level=info)
  --wfail               fail build if warnings are logged
                        (same as --fail-level=warning)


See `lake help <command>` for more information on a specific command."

def templateHelp :=
s!"The initial configuration and starter files are based on the template:

  std                   library and executable; default
  exe                   executable only
  lib                   library only
  math                  library only with a mathlib dependency

Templates can be suffixed with `.lean` or `.toml` to produce a Lean or TOML
version of the configuration file, respectively. The default is Lean."

def helpNew :=
s!"Create a Lean package in a new directory

USAGE:
  lake new <name> [<template>][.<language>]

{templateHelp}"

def helpInit :=
s!"Create a Lean package in the current directory

USAGE:
  lake init [<name>] [<template>][.<language>]

{templateHelp}

You can create a package with current directory's name via `lake init .`
or a bare `lake init`."

def helpBuild :=
"Build targets

USAGE:
  lake build [<targets>...]

A target is specified with a string of the form:

  [[@]<package>/][<target>|[+]<module>][:<facet>]

The optional `@` and `+` markers can be used to disambiguate packages
and modules from other kinds of targets (i.e., executables and libraries).

LIBRARY FACETS:         build the library's ...
  leanArts (default)    Lean artifacts (*.olean, *.ilean, *.c files)
  static                static artifact (*.a file)
  shared                shared artifact (*.so, *.dll, or *.dylib file)

MODULE FACETS:          build the module's ...
  deps                  dependencies (e.g., imports, shared libraries, etc.)
  leanArts (default)    Lean artifacts (*.olean, *.ilean, *.c files)
  olean                 OLean (binary blob of Lean data for importers)
  ilean                 ILean (binary blob of metadata for the Lean LSP server)
  c                     compiled C file
  bc                    compiled LLVM bitcode file
  c.o                   compiled object file (of its C file)
  bc.o                  compiled object file (of its LLVM bitcode file)
  o                     compiled object file (of its configured backend)
  dynlib                shared library (e.g., for `--load-dynlib`)

TARGET EXAMPLES:        build the ...
  a                     default facet of target `a`
  @a                    default target(s) of package `a`
  +A                    Lean artifacts of module `A`
  a/b                   default facet of target `b` of package `a`
  a/+A:c                C file of module `A` of package `a`
  :foo                  facet `foo` of the root package

A bare `lake build` command will build the default facet of the root package.
Package dependencies are not updated during a build."

def helpCheckBuild :=
"Check if any default build targets are configured

USAGE:
  lake check-build

Exits with code 0 if the workspace's root package has any
default targets configured. Errors (with code 1) otherwise.

Does NOT verify that the configured default targets are valid.
It merely verifies that some are specified.
"

def helpUpdate :=
"Update dependencies and save them to the manifest

USAGE:
  lake update [<package>...]

ALIAS: lake upgrade

Updates the Lake package manifest (i.e., `lake-manifest.json`),
downloading and upgrading packages as needed. For each new (transitive) git
dependency, the appropriate commit is cloned into a subdirectory of
`packagesDir`. No copy is made of local dependencies.

If a set of packages are specified, said dependencies are upgraded to
the latest version compatible with the package's configuration (or removed if
removed from the configuration). If there are dependencies on multiple versions
of the same package, the version materialized is undefined.

A bare `lake update` will upgrade all dependencies."

def helpTest :=
"Test the workspace's root package using its configured test driver

USAGE:
  lake test [-- <args>...]

A test driver can be configured by either setting the 'testDriver'
package configuration option or by tagging a script, executable, or library
`@[test_driver]`. A definition in a dependency can be used as a test driver
by using the `<pkg>/<name>` syntax for the 'testDriver' configuration option.

A script test driver will be run with the  package configuration's
`testDriverArgs` plus the CLI `args`. An executable test driver will be
built and then run like a script. A library test driver will just be built.
"

def helpCheckTest :=
"Check if there is a properly configured test driver

USAGE:
  lake check-test

Exits with code 0 if the workspace's root package has a properly
configured lint driver. Errors (with code 1) otherwise.

Does NOT verify that the configured test driver actually exists in the
package or its dependencies. It merely verifies that one is specified.
"

def helpLint :=
"Lint the workspace's root package using its configured lint driver

USAGE:
  lake lint [-- <args>...]

A lint driver can be configured by either setting the `lintDriver` package
configuration option by tagging a script or executable `@[lint_driver]`.
A definition in dependency can be used as a test driver by using the
`<pkg>/<name>` syntax for the 'testDriver' configuration option.

A script lint driver will be run with the  package configuration's
`lintDriverArgs` plus the CLI `args`. An executable lint driver will be
built and then run like a script.
"

def helpCheckLint :=
"Check if there is a properly configured lint driver

USAGE:
  lake check-lint

Exits with code 0 if the workspace's root package has a properly
configured lint driver. Errors (with code 1) otherwise.

Does NOT verify that the configured lint driver actually exists in the
package or its dependencies. It merely verifies that one is specified.
"

def helpPack :=
"Pack build artifacts into a archive for distribution

USAGE:
  lake pack [<file.tgz>]

Packs the root package's `buildDir` into a gzip tar archive using `tar`.
If a path for the archive is not specified, creates a archive in the package's
Lake directory (`.lake`) named according to its `buildArchive` setting.

Does NOT build any artifacts. It just packs the existing ones."

def helpUnpack :=
"Unpack build artifacts from a distributed archive

USAGE:
  lake unpack [<file.tgz>]

Unpack build artifacts from the gzip tar archive `file.tgz` into the root
package's `buildDir`. If a path for the archive is not specified, uses the
the package's `buildArchive` in its Lake directory (`.lake`)."

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

ALIAS: lake scripts

This command prints the list of all available scripts in the workspace."

def helpScriptRun :=
"Run a script

USAGE:
  lake script run [[<package>/]<script>] [<args>...]

ALIAS: lake run

This command runs the `script` of the workspace (or the specific `package`),
passing `args` to it.

A bare `lake run` command will run the default script(s) of the root package
(with no arguments)."

def helpScriptDoc :=
"Print a script's docstring

USAGE:
  lake script doc [<package>/]<script>

Print the docstring of `script` in the workspace or the specific `package`."

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

ALIAS: lake exec

Looks for the executable target in the workspace (see `lake help build` to
learn how to specify targets), builds it if it is out of date, and then runs
it with the given `args` in Lake's environment (see `lake help env` for how
the environment is set up)."

def helpLean :=
"Elaborate a Lean file in the context of the Lake workspace

USAGE:
  lake lean <file> [-- <args>...]

Build the imports of the given file and then runs `lean` on it using
the workspace's root package's additional Lean arguments and the given args
(in that order). The `lean` process is executed in Lake's environment like
`lake env lean` (see `lake help env` for how the environment is set up)."

def helpTranslateConfig :=
"Translate a Lake configuration file into a different language

USAGE:
  lake translate-config <lang> [<out-file>]

Translates the loaded package's configuration into another of
Lake's supported configuration languages (i.e., either `lean` or `toml`).
The produced file is written to `out-file` or, if not provided, the path of
the configuration file with the new language's extension. If the output file
already exists, Lake will error.

Translation is lossy. It does not preserve comments or formatting and
non-declarative configuration will be discarded."

def helpScript : (cmd : String) → String
| "list"                => helpScriptList
| "run"                 => helpScriptRun
| "doc"                 => helpScriptDoc
| _                     => helpScriptCli

def help : (cmd : String) → String
| "new"                 => helpNew
| "init"                => helpInit
| "build"               => helpBuild
| "check-build"         => helpCheckBuild
| "update" | "upgrade"  => helpUpdate
| "pack"                => helpPack
| "unpack"              => helpUnpack
| "upload"              => helpUpload
| "test"                => helpTest
| "check-test"          => helpCheckTest
| "lint"                => helpLint
| "check-lint"          => helpCheckLint
| "clean"               => helpClean
| "script"              => helpScriptCli
| "scripts"             => helpScriptList
| "run"                 => helpScriptRun
| "serve"               => helpServe
| "env"                 => helpEnv
| "exe" | "exec"        => helpExe
| "lean"                => helpLean
| "translate-config"    => helpTranslateConfig
| _                     => usage
