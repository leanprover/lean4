/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Lake.Version

namespace Lake

def usage :=
uiVersionString ++ "\
\n\
\nUSAGE:\
\n  lake [OPTIONS] <COMMAND>\
\n\
\nCOMMANDS:\
\n  new <name> <temp>     create a Lean package in a new directory\
\n  init <name> <temp>    create a Lean package in the current directory\
\n  build <targets>...    build targets\
\n  exe <exe> <args>...   build an exe and run it in Lake's environment\
\n  test                  test the package using the configured test driver\
\n  check-test            check if there is a properly configured test driver\
\n  lint                  lint the package using the configured lint driver\
\n  check-lint            check if there is a properly configured lint driver\
\n  clean                 remove build outputs\
\n  env <cmd> <args>...   execute a command in Lake's environment\
\n  lean <file>           elaborate a Lean file in Lake's context\
\n  update                update dependencies and save them to the manifest\
\n  pack                  pack build artifacts into an archive for distribution\
\n  unpack                unpack build artifacts from an distributed archive\
\n  upload <tag>          upload build artifacts to a GitHub release\
\n  script                manage and run workspace scripts\
\n  scripts               shorthand for `lake script list`\
\n  run <script>          shorthand for `lake script run`\
\n  translate-config      change language of the package configuration\
\n  serve                 start the Lean language server\
\n\
\nBASIC OPTIONS:\
\n  --version             print version and exit\
\n  --help, -h            print help of the program or a command and exit\
\n  --dir, -d=file        use the package configuration in a specific directory\
\n  --file, -f=file       use a specific file for the package configuration\
\n  --lean=cmd            specify the `lean` command used by Lake\
\n  -K key[=value]        set the configuration file option named key\
\n  --old                 only rebuild modified modules (ignore transitive deps)\
\n  --rehash, -H          hash all files for traces (do not trust `.hash` files)\
\n  --update, -U          update manifest before building\
\n  --reconfigure, -R     elaborate configuration files instead of using OLeans\
\n  --no-build            exit immediately if a build target is not up-to-date\
\n\
\nOUTPUT OPTIONS:\
\n  --quiet, -q           hide informational logs and the progress indicator\
\n  --verbose, -v         show trace logs (command invocations) and built targets\
\n  --ansi, --no-ansi     toggle the use of ANSI escape codes to prettify output\
\n  --log-level=lv        minimum log level to output on success\
\n                        (levels: trace, info, warning, error)\
\n  --fail-level=lv       minimum log level to fail a build (default: error)\
\n  --iofail              fail build if any I/O or other info is logged\
\n                        (same as --fail-level=info)\
\n  --wfail               fail build if warnings are logged\
\n                        (same as --fail-level=warning)\
\n\
\n\
\nSee `lake help <command>` for more information on a specific command."

def templateHelp :=
s!"The initial configuration and starter files are based on the template:\
\n\
\n  std                   library and executable; default\
\n  exe                   executable only\
\n  lib                   library only\
\n  math                  library only with a mathlib dependency\
\n\
\nTemplates can be suffixed with `.lean` or `.toml` to produce a Lean or TOML\
\nversion of the configuration file, respectively. The default is Lean."

def helpNew :=
s!"Create a Lean package in a new directory\
\n\
\nUSAGE:\
\n  lake new <name> [<template>][.<language>]\
\n\
\n{templateHelp}"

def helpInit :=
s!"Create a Lean package in the current directory\
\n\
\nUSAGE:\
\n  lake init [<name>] [<template>][.<language>]\
\n\
\n{templateHelp}\
\n\
\nYou can create a package with current directory's name via `lake init .`\
\nor a bare `lake init`."

def helpBuild :=
"Build targets\
\n\
\nUSAGE:\
\n  lake build [<targets>...]\
\n\
\nA target is specified with a string of the form:\
\n\
\n  [[@]<package>/][<target>|[+]<module>][:<facet>]\
\n\
\nThe optional `@` and `+` markers can be used to disambiguate packages\
\nand modules from other kinds of targets (i.e., executables and libraries).\
\n\
\nLIBRARY FACETS:         build the library's ...\
\n  leanArts (default)    Lean artifacts (*.olean, *.ilean, *.c files)\
\n  static                static artifact (*.a file)\
\n  shared                shared artifact (*.so, *.dll, or *.dylib file)\
\n\
\nMODULE FACETS:          build the module's ...\
\n  deps                  dependencies (e.g., imports, shared libraries, etc.)\
\n  leanArts (default)    Lean artifacts (*.olean, *.ilean, *.c files)\
\n  olean                 OLean (binary blob of Lean data for importers)\
\n  ilean                 ILean (binary blob of metadata for the Lean LSP server)\
\n  c                     compiled C file\
\n  bc                    compiled LLVM bitcode file\
\n  c.o                   compiled object file (of its C file)\
\n  bc.o                  compiled object file (of its LLVM bitcode file)\
\n  o                     compiled object file (of its configured backend)\
\n  dynlib                shared library (e.g., for `--load-dynlib`)\
\n\
\nTARGET EXAMPLES:        build the ...\
\n  a                     default facet of target `a`\
\n  @a                    default target(s) of package `a`\
\n  +A                    Lean artifacts of module `A`\
\n  a/b                   default facet of target `b` of package `a`\
\n  a/+A:c                C file of module `A` of package `a`\
\n  :foo                  facet `foo` of the root package\
\n\
\nA bare `lake build` command will build the default facet of the root package.\
\nPackage dependencies are not updated during a build."

def helpUpdate :=
"Update dependencies and save them to the manifest\
\n\
\nUSAGE:\
\n  lake update [<package>...]\
\n\
\nALIAS: lake upgrade\
\n\
\nUpdates the Lake package manifest (i.e., `lake-manifest.json`),\
\ndownloading and upgrading packages as needed. For each new (transitive) git\
\ndependency, the appropriate commit is cloned into a subdirectory of\
\n`packagesDir`. No copy is made of local dependencies.\
\n\
\nIf a set of packages are specified, said dependencies are upgraded to\
\nthe latest version compatible with the package's configuration (or removed if\
\nremoved from the configuration). If there are dependencies on multiple versions\
\nof the same package, the version materialized is undefined.\
\n\
\nA bare `lake update` will upgrade all dependencies."

def helpTest :=
"Test the workspace's root package using its configured test driver\
\n\
\nUSAGE:\
\n  lake test [-- <args>...]\
\n\
\nA test driver can be configured by either setting the 'testDriver'\
\npackage configuration option or by tagging a script, executable, or library\
\n`@[test_driver]`. A definition in a dependency can be used as a test driver\
\nby using the `<pkg>/<name>` syntax for the 'testDriver' configuration option.\
\n\
\nA script test driver will be run with the  package configuration's\
\n`testDriverArgs` plus the CLI `args`. An executable test driver will be\
\nbuilt and then run like a script. A library test driver will just be built.\
\n"

def helpCheckTest :=
"Check if there is a properly configured test driver\
\n\
\nUSAGE:\
\n  lake check-test\
\n\
\nExits with code 0 if the workspace's root package has a properly\
\nconfigured lint driver. Errors (with code 1) otherwise.\
\n\
\nDoes NOT verify that the configured test driver actually exists in the\
\npackage or its dependencies. It merely verifies that one is specified.\
\n"

def helpLint :=
"Lint the workspace's root package using its configured lint driver\
\n\
\nUSAGE:\
\n  lake lint [-- <args>...]\
\n\
\nA lint driver can be configured by either setting the `lintDriver` package\
\nconfiguration option by tagging a script or executable `@[lint_driver]`.\
\nA definition in dependency can be used as a test driver by using the\
\n`<pkg>/<name>` syntax for the 'testDriver' configuration option.\
\n\
\nA script lint driver will be run with the  package configuration's\
\n`lintDriverArgs` plus the CLI `args`. An executable lint driver will be\
\nbuilt and then run like a script.\
\n"

def helpCheckLint :=
"Check if there is a properly configured lint driver\
\n\
\nUSAGE:\
\n  lake check-lint\
\n\
\nExits with code 0 if the workspace's root package has a properly\
\nconfigured lint driver. Errors (with code 1) otherwise.\
\n\
\nDoes NOT verify that the configured lint driver actually exists in the\
\npackage or its dependencies. It merely verifies that one is specified.\
\n"

def helpPack :=
"Pack build artifacts into a archive for distribution\
\n\
\nUSAGE:\
\n  lake pack [<file.tgz>]\
\n\
\nPacks the root package's `buildDir` into a gzip tar archive using `tar`.\
\nIf a path for the archive is not specified, creates a archive in the package's\
\nLake directory (`.lake`) named according to its `buildArchive` setting.\
\n\
\nDoes NOT build any artifacts. It just packs the existing ones."

def helpUnpack :=
"Unpack build artifacts from a distributed archive\
\n\
\nUSAGE:\
\n  lake unpack [<file.tgz>]\
\n\
\nUnpack build artifacts from the gzip tar archive `file.tgz` into the root\
\npackage's `buildDir`. If a path for the archive is not specified, uses the\
\nthe package's `buildArchive` in its Lake directory (`.lake`)."

def helpUpload :=
"Upload build artifacts to a GitHub release\
\n\
\nUSAGE:\
\n  lake upload <tag>\
\n\
\nPacks the root package's `buildDir` into a `tar.gz` archive using `tar` and\
\nthen uploads the asset to the pre-existing GitHub release `tag` using `gh`."

def helpClean :=
"Remove build outputs\
\n\
\nUSAGE:\
\n  lake clean [<package>...]\
\n\
\nIf no package is specified, deletes the build directories of every package in\
\nthe workspace. Otherwise, just deletes those of the specified packages."

def helpScriptCli :=
"Manage Lake scripts\
\n\
\nUSAGE:\
\n  lake script <COMMAND>\
\n\
\nCOMMANDS:\
\n  list                  list available scripts\
\n  run <script>          run a script\
\n  doc <script>          print the docstring of a given script\
\n\
\nSee `lake help <command>` for more information on a specific command."

def helpScriptList :=
"List available scripts\
\n\
\nUSAGE:\
\n  lake script list\
\n\
\nALIAS: lake scripts\
\n\
\nThis command prints the list of all available scripts in the workspace."

def helpScriptRun :=
"Run a script\
\n\
\nUSAGE:\
\n  lake script run [[<package>/]<script>] [<args>...]\
\n\
\nALIAS: lake run\
\n\
\nThis command runs the `script` of the workspace (or the specific `package`),\
\npassing `args` to it.\
\n\
\nA bare `lake run` command will run the default script(s) of the root package\
\n(with no arguments)."

def helpScriptDoc :=
"Print a script's docstring\
\n\
\nUSAGE:\
\n  lake script doc [<package>/]<script>\
\n\
\nPrint the docstring of `script` in the workspace or the specific `package`."

def helpServe :=
"Start the Lean language server\
\n\
\nUSAGE:\
\n  lake serve [-- <args>...]\
\n\
\nRun the language server of the Lean installation (i.e., via `lean --server`)\
\nwith the package configuration's `moreServerArgs` field and `args`.\
\n"

def helpEnv :=
"Execute a command in Lake's environment\
\n\
\nUSAGE:\
\n  lake env [<cmd>] [<args>...]\
\n\
\nSpawns a new process executing `cmd` with the given `args` and with\
\nthe environment set based on the detected Lean/Lake installations and\
\nthe workspace configuration (if it exists).\
\n\
\nSpecifically, this command sets the following environment variables:\
\n\
\n  LAKE                  set to the detected Lake executable\
\n  LAKE_HOME             set to the detected Lake home\
\n  LEAN_SYSROOT          set to the detected Lean toolchain directory\
\n  LEAN_AR               set to the detected Lean `ar` binary\
\n  LEAN_CC               set to the detected `cc` (if not using the bundled one)\
\n  LEAN_PATH             adds Lake's and the workspace's Lean library dirs\
\n  LEAN_SRC_PATH         adds Lake's and the workspace's source dirs\
\n  PATH                  adds Lean's, Lake's, and the workspace's binary dirs\
\n  PATH                  adds Lean's and the workspace's library dirs (Windows)\
\n  DYLD_LIBRARY_PATH     adds Lean's and the workspace's library dirs (MacOS)\
\n  LD_LIBRARY_PATH       adds Lean's and the workspace's library dirs (other)\
\n\
\nA bare `lake env` will print out the variables set and their values,\
\nusing the form NAME=VALUE like the POSIX `env` command."

def helpExe :=
"Build an executable target and run it in Lake's environment\
\n\
\nUSAGE:\
\n  lake exe <exe-target> [<args>...]\
\n\
\nALIAS: lake exec\
\n\
\nLooks for the executable target in the workspace (see `lake help build` to\
\nlearn how to specify targets), builds it if it is out of date, and then runs\
\nit with the given `args` in Lake's environment (see `lake help env` for how\
\nthe environment is set up)."

def helpLean :=
"Elaborate a Lean file in the context of the Lake workspace\
\n\
\nUSAGE:\
\n  lake lean <file> [-- <args>...]\
\n\
\nBuild the imports of the the given file and then runs `lean` on it using\
\nthe workspace's root package's additional Lean arguments and the given args\
\n(in that order). The `lean` process is executed in Lake's environment like\
\n`lake env lean` (see `lake help env` for how the environment is set up)."

def helpTranslateConfig :=
"Translate a Lake configuration file into a different language\
\n\
\nUSAGE:\
\n  lake translate-config <lang> [<out-file>]\
\n\
\nTranslates the loaded package's configuration into another of\
\nLake's supported configuration languages (i.e., either `lean` or `toml`).\
\nThe produced file is written to `out-file` or, if not provided, the path of\
\nthe configuration file with the new language's extension. If the output file\
\nalready exists, Lake will error.\
\n\
\nTranslation is lossy. It does not preserve comments or formatting and\
\nnon-declarative configuration will be discarded."

def helpScript : (cmd : String) → String
| "list"                => helpScriptList
| "run"                 => helpScriptRun
| "doc"                 => helpScriptDoc
| _                     => helpScriptCli

def help : (cmd : String) → String
| "new"                 => helpNew
| "init"                => helpInit
| "build"               => helpBuild
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
