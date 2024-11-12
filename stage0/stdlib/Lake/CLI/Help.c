// Lean compiler output
// Module: Lake.CLI.Help
// Imports: Init Lake.Version
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
static lean_object* l_Lake_help___closed__18;
static lean_object* l_Lake_help___closed__2;
static lean_object* l_Lake_helpInit___closed__1;
static lean_object* l_Lake_helpClean___closed__1;
static lean_object* l_Lake_helpServe___closed__1;
static lean_object* l_Lake_help___closed__3;
LEAN_EXPORT lean_object* l_Lake_helpPack;
LEAN_EXPORT lean_object* l_Lake_help(lean_object*);
static lean_object* l_Lake_helpInit___closed__3;
static lean_object* l_Lake_help___closed__17;
LEAN_EXPORT lean_object* l_Lake_helpEnv;
LEAN_EXPORT lean_object* l_Lake_helpLint;
LEAN_EXPORT lean_object* l_Lake_helpCheckTest;
static lean_object* l_Lake_helpScript___closed__3;
static lean_object* l_Lake_help___closed__16;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lake_help___closed__1;
LEAN_EXPORT lean_object* l_Lake_helpCheckLint;
LEAN_EXPORT lean_object* l_Lake_helpBuild;
static lean_object* l_Lake_helpScript___closed__1;
static lean_object* l_Lake_helpUpdate___closed__1;
static lean_object* l_Lake_help___closed__13;
LEAN_EXPORT lean_object* l_Lake_usage;
LEAN_EXPORT lean_object* l_Lake_help___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_helpScript(lean_object*);
static lean_object* l_Lake_help___closed__8;
LEAN_EXPORT lean_object* l_Lake_helpScriptRun;
LEAN_EXPORT lean_object* l_Lake_helpTest;
static lean_object* l_Lake_helpNew___closed__1;
static lean_object* l_Lake_help___closed__22;
LEAN_EXPORT lean_object* l_Lake_helpUpload;
static lean_object* l_Lake_helpLint___closed__1;
static lean_object* l_Lake_help___closed__20;
LEAN_EXPORT lean_object* l_Lake_helpTranslateConfig;
LEAN_EXPORT lean_object* l_Lake_helpServe;
static lean_object* l_Lake_helpInit___closed__2;
static lean_object* l_Lake_helpPack___closed__1;
static lean_object* l_Lake_helpScriptDoc___closed__1;
static lean_object* l_Lake_help___closed__4;
static lean_object* l_Lake_helpCheckTest___closed__1;
static lean_object* l_Lake_help___closed__15;
static lean_object* l_Lake_help___closed__10;
static lean_object* l_Lake_helpInit___closed__4;
static lean_object* l_Lake_help___closed__21;
static lean_object* l_Lake_helpLean___closed__1;
static lean_object* l_Lake_helpTranslateConfig___closed__1;
static lean_object* l_Lake_helpBuild___closed__1;
static lean_object* l_Lake_helpExe___closed__1;
LEAN_EXPORT lean_object* l_Lake_helpLean;
static lean_object* l_Lake_help___closed__9;
static lean_object* l_Lake_helpUnpack___closed__1;
static lean_object* l_Lake_help___closed__7;
LEAN_EXPORT lean_object* l_Lake_helpScriptDoc;
static lean_object* l_Lake_helpTest___closed__1;
static lean_object* l_Lake_help___closed__12;
static lean_object* l_Lake_helpNew___closed__4;
LEAN_EXPORT lean_object* l_Lake_helpNew;
static lean_object* l_Lake_helpScriptRun___closed__1;
LEAN_EXPORT lean_object* l_Lake_helpExe;
LEAN_EXPORT lean_object* l_Lake_helpScriptList;
static lean_object* l_Lake_helpEnv___closed__1;
LEAN_EXPORT lean_object* l_Lake_helpInit;
static lean_object* l_Lake_helpCheckBuild___closed__1;
static lean_object* l_Lake_helpNew___closed__2;
LEAN_EXPORT lean_object* l_Lake_helpUnpack;
LEAN_EXPORT lean_object* l_Lake_helpUpdate;
LEAN_EXPORT lean_object* l_Lake_helpScript___boxed(lean_object*);
static lean_object* l_Lake_helpScript___closed__2;
static lean_object* l_Lake_help___closed__5;
static lean_object* l_Lake_helpCheckLint___closed__1;
static lean_object* l_Lake_helpNew___closed__3;
static lean_object* l_Lake_templateHelp___closed__1;
static lean_object* l_Lake_helpUpload___closed__1;
static lean_object* l_Lake_helpScriptList___closed__1;
static lean_object* l_Lake_usage___closed__2;
static lean_object* l_Lake_help___closed__14;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lake_help___closed__11;
static lean_object* l_Lake_help___closed__6;
static lean_object* l_Lake_helpScriptCli___closed__1;
LEAN_EXPORT lean_object* l_Lake_helpCheckBuild;
LEAN_EXPORT lean_object* l_Lake_templateHelp;
static lean_object* l_Lake_help___closed__19;
static lean_object* l_Lake_usage___closed__1;
LEAN_EXPORT lean_object* l_Lake_helpClean;
extern lean_object* l_Lake_uiVersionString;
LEAN_EXPORT lean_object* l_Lake_helpScriptCli;
static lean_object* _init_l_Lake_usage___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n\nUSAGE:\n  lake [OPTIONS] <COMMAND>\n\nCOMMANDS:\n  new <name> <temp>     create a Lean package in a new directory\n  init <name> <temp>    create a Lean package in the current directory\n  build <targets>...    build targets\n  exe <exe> <args>...   build an exe and run it in Lake's environment\n  check-build           check if any default build targets are configured\n  test                  test the package using the configured test driver\n  check-test            check if there is a properly configured test driver\n  lint                  lint the package using the configured lint driver\n  check-lint            check if there is a properly configured lint driver\n  clean                 remove build outputs\n  env <cmd> <args>...   execute a command in Lake's environment\n  lean <file>           elaborate a Lean file in Lake's context\n  update                update dependencies and save them to the manifest\n  pack                  pack build artifacts into an archive for distribution\n  unpack                unpack build artifacts from an distributed archive\n  upload <tag>          upload build artifacts to a GitHub release\n  script                manage and run workspace scripts\n  scripts               shorthand for `lake script list`\n  run <script>          shorthand for `lake script run`\n  translate-config      change language of the package configuration\n  serve                 start the Lean language server\n\nBASIC OPTIONS:\n  --version             print version and exit\n  --help, -h            print help of the program or a command and exit\n  --dir, -d=file        use the package configuration in a specific directory\n  --file, -f=file       use a specific file for the package configuration\n  -K key[=value]        set the configuration file option named key\n  --old                 only rebuild modified modules (ignore transitive deps)\n  --rehash, -H          hash all files for traces (do not trust `.hash` files)\n  --update, -U          update dependencies on load (e.g., before a build)\n  --reconfigure, -R     elaborate configuration files instead of using OLeans\n  --keep-toolchain      do not update toolchain on workspace update\n  --no-build            exit immediately if a build target is not up-to-date\n  --no-cache            build packages locally; do not download build caches\n  --try-cache           attempt to download build caches for supported packages\n\nOUTPUT OPTIONS:\n  --quiet, -q           hide informational logs and the progress indicator\n  --verbose, -v         show trace logs (command invocations) and built targets\n  --ansi, --no-ansi     toggle the use of ANSI escape codes to prettify output\n  --log-level=lv        minimum log level to output on success\n                        (levels: trace, info, warning, error)\n  --fail-level=lv       minimum log level to fail a build (default: error)\n  --iofail              fail build if any I/O or other info is logged\n                        (same as --fail-level=info)\n  --wfail               fail build if warnings are logged\n                        (same as --fail-level=warning)\n\n\nSee `lake help <command>` for more information on a specific command.", 3151, 3151);
return x_1;
}
}
static lean_object* _init_l_Lake_usage___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_uiVersionString;
x_2 = l_Lake_usage___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_usage() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_usage___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lake_templateHelp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("The initial configuration and starter files are based on the template:\n\n  std                   library and executable; default\n  exe                   executable only\n  lib                   library only\n  math                  library only with a mathlib dependency\n\nTemplates can be suffixed with `.lean` or `.toml` to produce a Lean or TOML\nversion of the configuration file, respectively. The default is Lean.", 414, 414);
return x_1;
}
}
static lean_object* _init_l_Lake_templateHelp() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_templateHelp___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_helpNew___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Create a Lean package in a new directory\n\nUSAGE:\n  lake new <name> [<template>][.<language>]\n\n", 94, 94);
return x_1;
}
}
static lean_object* _init_l_Lake_helpNew___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_helpNew___closed__1;
x_2 = l_Lake_templateHelp;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_helpNew___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_helpNew___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_helpNew___closed__2;
x_2 = l_Lake_helpNew___closed__3;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_helpNew() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_helpNew___closed__4;
return x_1;
}
}
static lean_object* _init_l_Lake_helpInit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Create a Lean package in the current directory\n\nUSAGE:\n  lake init [<name>] [<template>][.<language>]\n\n", 103, 103);
return x_1;
}
}
static lean_object* _init_l_Lake_helpInit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_helpInit___closed__1;
x_2 = l_Lake_templateHelp;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_helpInit___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n\nYou can create a package with current directory's name via `lake init .`\nor a bare `lake init`.", 97, 97);
return x_1;
}
}
static lean_object* _init_l_Lake_helpInit___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_helpInit___closed__2;
x_2 = l_Lake_helpInit___closed__3;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_helpInit() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_helpInit___closed__4;
return x_1;
}
}
static lean_object* _init_l_Lake_helpBuild___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Build targets\n\nUSAGE:\n  lake build [<targets>...]\n\nA target is specified with a string of the form:\n\n  [[@]<package>/][<target>|[+]<module>][:<facet>]\n\nThe optional `@` and `+` markers can be used to disambiguate packages\nand modules from other kinds of targets (i.e., executables and libraries).\n\nLIBRARY FACETS:         build the library's ...\n  leanArts (default)    Lean artifacts (*.olean, *.ilean, *.c files)\n  static                static artifact (*.a file)\n  shared                shared artifact (*.so, *.dll, or *.dylib file)\n\nMODULE FACETS:          build the module's ...\n  deps                  dependencies (e.g., imports, shared libraries, etc.)\n  leanArts (default)    Lean artifacts (*.olean, *.ilean, *.c files)\n  olean                 OLean (binary blob of Lean data for importers)\n  ilean                 ILean (binary blob of metadata for the Lean LSP server)\n  c                     compiled C file\n  bc                    compiled LLVM bitcode file\n  c.o                   compiled object file (of its C file)\n  bc.o                  compiled object file (of its LLVM bitcode file)\n  o                     compiled object file (of its configured backend)\n  dynlib                shared library (e.g., for `--load-dynlib`)\n\nTARGET EXAMPLES:        build the ...\n  a                     default facet of target `a`\n  @a                    default target(s) of package `a`\n  +A                    Lean artifacts of module `A`\n  a/b                   default facet of target `b` of package `a`\n  a/+A:c                C file of module `A` of package `a`\n  :foo                  facet `foo` of the root package\n\nA bare `lake build` command will build the default facet of the root package.\nPackage dependencies are not updated during a build.", 1761, 1761);
return x_1;
}
}
static lean_object* _init_l_Lake_helpBuild() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_helpBuild___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_helpCheckBuild___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Check if any default build targets are configured\n\nUSAGE:\n  lake check-build\n\nExits with code 0 if the workspace's root package has any\ndefault targets configured. Errors (with code 1) otherwise.\n\nDoes NOT verify that the configured default targets are valid.\nIt merely verifies that some are specified.\n", 304, 304);
return x_1;
}
}
static lean_object* _init_l_Lake_helpCheckBuild() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_helpCheckBuild___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_helpUpdate___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Update dependencies and save them to the manifest\n\nUSAGE:\n  lake update [<package>...]\n\nALIAS: lake upgrade\n\nUpdates the Lake package manifest (i.e., `lake-manifest.json`),\ndownloading and upgrading packages as needed. For each new (transitive) git\ndependency, the appropriate commit is cloned into a subdirectory of\n`packagesDir`. No copy is made of local dependencies.\n\nIf a set of packages are specified, said dependencies are upgraded to\nthe latest version compatible with the package's configuration (or removed if\nremoved from the configuration). If there are dependencies on multiple versions\nof the same package, the version materialized is undefined.\n\nA bare `lake update` will upgrade all dependencies.", 712, 712);
return x_1;
}
}
static lean_object* _init_l_Lake_helpUpdate() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_helpUpdate___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_helpTest___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Test the workspace's root package using its configured test driver\n\nUSAGE:\n  lake test [-- <args>...]\n\nA test driver can be configured by either setting the 'testDriver'\npackage configuration option or by tagging a script, executable, or library\n`@[test_driver]`. A definition in a dependency can be used as a test driver\nby using the `<pkg>/<name>` syntax for the 'testDriver' configuration option.\n\nA script test driver will be run with the  package configuration's\n`testDriverArgs` plus the CLI `args`. An executable test driver will be\nbuilt and then run like a script. A library test driver will just be built.\n", 616, 616);
return x_1;
}
}
static lean_object* _init_l_Lake_helpTest() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_helpTest___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_helpCheckTest___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Check if there is a properly configured test driver\n\nUSAGE:\n  lake check-test\n\nExits with code 0 if the workspace's root package has a properly\nconfigured lint driver. Errors (with code 1) otherwise.\n\nDoes NOT verify that the configured test driver actually exists in the\npackage or its dependencies. It merely verifies that one is specified.\n", 343, 343);
return x_1;
}
}
static lean_object* _init_l_Lake_helpCheckTest() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_helpCheckTest___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_helpLint___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lint the workspace's root package using its configured lint driver\n\nUSAGE:\n  lake lint [-- <args>...]\n\nA lint driver can be configured by either setting the `lintDriver` package\nconfiguration option by tagging a script or executable `@[lint_driver]`.\nA definition in dependency can be used as a test driver by using the\n`<pkg>/<name>` syntax for the 'testDriver' configuration option.\n\nA script lint driver will be run with the  package configuration's\n`lintDriverArgs` plus the CLI `args`. An executable lint driver will be\nbuilt and then run like a script.\n", 559, 559);
return x_1;
}
}
static lean_object* _init_l_Lake_helpLint() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_helpLint___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_helpCheckLint___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Check if there is a properly configured lint driver\n\nUSAGE:\n  lake check-lint\n\nExits with code 0 if the workspace's root package has a properly\nconfigured lint driver. Errors (with code 1) otherwise.\n\nDoes NOT verify that the configured lint driver actually exists in the\npackage or its dependencies. It merely verifies that one is specified.\n", 343, 343);
return x_1;
}
}
static lean_object* _init_l_Lake_helpCheckLint() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_helpCheckLint___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_helpPack___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Pack build artifacts into a archive for distribution\n\nUSAGE:\n  lake pack [<file.tgz>]\n\nPacks the root package's `buildDir` into a gzip tar archive using `tar`.\nIf a path for the archive is not specified, creates a archive in the package's\nLake directory (`.lake`) named according to its `buildArchive` setting.\n\nDoes NOT build any artifacts. It just packs the existing ones.", 374, 374);
return x_1;
}
}
static lean_object* _init_l_Lake_helpPack() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_helpPack___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_helpUnpack___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Unpack build artifacts from a distributed archive\n\nUSAGE:\n  lake unpack [<file.tgz>]\n\nUnpack build artifacts from the gzip tar archive `file.tgz` into the root\npackage's `buildDir`. If a path for the archive is not specified, uses the\nthe package's `buildArchive` in its Lake directory (`.lake`).", 296, 296);
return x_1;
}
}
static lean_object* _init_l_Lake_helpUnpack() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_helpUnpack___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_helpUpload___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Upload build artifacts to a GitHub release\n\nUSAGE:\n  lake upload <tag>\n\nPacks the root package's `buildDir` into a `tar.gz` archive using `tar` and\nthen uploads the asset to the pre-existing GitHub release `tag` using `gh`.", 223, 223);
return x_1;
}
}
static lean_object* _init_l_Lake_helpUpload() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_helpUpload___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_helpClean___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Remove build outputs\n\nUSAGE:\n  lake clean [<package>...]\n\nIf no package is specified, deletes the build directories of every package in\nthe workspace. Otherwise, just deletes those of the specified packages.", 207, 207);
return x_1;
}
}
static lean_object* _init_l_Lake_helpClean() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_helpClean___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_helpScriptCli___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Manage Lake scripts\n\nUSAGE:\n  lake script <COMMAND>\n\nCOMMANDS:\n  list                  list available scripts\n  run <script>          run a script\n  doc <script>          print the docstring of a given script\n\nSee `lake help <command>` for more information on a specific command.", 279, 279);
return x_1;
}
}
static lean_object* _init_l_Lake_helpScriptCli() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_helpScriptCli___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_helpScriptList___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("List available scripts\n\nUSAGE:\n  lake script list\n\nALIAS: lake scripts\n\nThis command prints the list of all available scripts in the workspace.", 143, 143);
return x_1;
}
}
static lean_object* _init_l_Lake_helpScriptList() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_helpScriptList___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_helpScriptRun___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Run a script\n\nUSAGE:\n  lake script run [[<package>/]<script>] [<args>...]\n\nALIAS: lake run\n\nThis command runs the `script` of the workspace (or the specific `package`),\npassing `args` to it.\n\nA bare `lake run` command will run the default script(s) of the root package\n(with no arguments).", 289, 289);
return x_1;
}
}
static lean_object* _init_l_Lake_helpScriptRun() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_helpScriptRun___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_helpScriptDoc___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Print a script's docstring\n\nUSAGE:\n  lake script doc [<package>/]<script>\n\nPrint the docstring of `script` in the workspace or the specific `package`.", 150, 150);
return x_1;
}
}
static lean_object* _init_l_Lake_helpScriptDoc() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_helpScriptDoc___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_helpServe___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Start the Lean language server\n\nUSAGE:\n  lake serve [-- <args>...]\n\nRun the language server of the Lean installation (i.e., via `lean --server`)\nwith the package configuration's `moreServerArgs` field and `args`.\n", 213, 213);
return x_1;
}
}
static lean_object* _init_l_Lake_helpServe() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_helpServe___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_helpEnv___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Execute a command in Lake's environment\n\nUSAGE:\n  lake env [<cmd>] [<args>...]\n\nSpawns a new process executing `cmd` with the given `args` and with\nthe environment set based on the detected Lean/Lake installations and\nthe workspace configuration (if it exists).\n\nSpecifically, this command sets the following environment variables:\n\n  LAKE                  set to the detected Lake executable\n  LAKE_HOME             set to the detected Lake home\n  LEAN_SYSROOT          set to the detected Lean toolchain directory\n  LEAN_AR               set to the detected Lean `ar` binary\n  LEAN_CC               set to the detected `cc` (if not using the bundled one)\n  LEAN_PATH             adds Lake's and the workspace's Lean library dirs\n  LEAN_SRC_PATH         adds Lake's and the workspace's source dirs\n  PATH                  adds Lean's, Lake's, and the workspace's binary dirs\n  PATH                  adds Lean's and the workspace's library dirs (Windows)\n  DYLD_LIBRARY_PATH     adds Lean's and the workspace's library dirs (MacOS)\n  LD_LIBRARY_PATH       adds Lean's and the workspace's library dirs (other)\n\nA bare `lake env` will print out the variables set and their values,\nusing the form NAME=VALUE like the POSIX `env` command.", 1234, 1234);
return x_1;
}
}
static lean_object* _init_l_Lake_helpEnv() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_helpEnv___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_helpExe___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Build an executable target and run it in Lake's environment\n\nUSAGE:\n  lake exe <exe-target> [<args>...]\n\nALIAS: lake exec\n\nLooks for the executable target in the workspace (see `lake help build` to\nlearn how to specify targets), builds it if it is out of date, and then runs\nit with the given `args` in Lake's environment (see `lake help env` for how\nthe environment is set up).", 378, 378);
return x_1;
}
}
static lean_object* _init_l_Lake_helpExe() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_helpExe___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_helpLean___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elaborate a Lean file in the context of the Lake workspace\n\nUSAGE:\n  lake lean <file> [-- <args>...]\n\nBuild the imports of the given file and then runs `lean` on it using\nthe workspace's root package's additional Lean arguments and the given args\n(in that order). The `lean` process is executed in Lake's environment like\n`lake env lean` (see `lake help env` for how the environment is set up).", 394, 394);
return x_1;
}
}
static lean_object* _init_l_Lake_helpLean() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_helpLean___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_helpTranslateConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Translate a Lake configuration file into a different language\n\nUSAGE:\n  lake translate-config <lang> [<out-file>]\n\nTranslates the loaded package's configuration into another of\nLake's supported configuration languages (i.e., either `lean` or `toml`).\nThe produced file is written to `out-file` or, if not provided, the path of\nthe configuration file with the new language's extension. If the output file\nalready exists, Lake will error.\n\nTranslation is lossy. It does not preserve comments or formatting and\nnon-declarative configuration will be discarded.", 556, 556);
return x_1;
}
}
static lean_object* _init_l_Lake_helpTranslateConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_helpTranslateConfig___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_helpScript___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("list", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_helpScript___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("run", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_helpScript___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("doc", 3, 3);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_helpScript(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lake_helpScript___closed__1;
x_3 = lean_string_dec_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lake_helpScript___closed__2;
x_5 = lean_string_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lake_helpScript___closed__3;
x_7 = lean_string_dec_eq(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = l_Lake_helpScriptCli;
return x_8;
}
else
{
lean_object* x_9; 
x_9 = l_Lake_helpScriptDoc;
return x_9;
}
}
else
{
lean_object* x_10; 
x_10 = l_Lake_helpScriptRun;
return x_10;
}
}
else
{
lean_object* x_11; 
x_11 = l_Lake_helpScriptList;
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lake_helpScript___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_helpScript(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_help___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("new", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_help___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("init", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_help___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("build", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_help___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("check-build", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lake_help___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("update", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_help___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("upgrade", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_help___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("pack", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_help___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unpack", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_help___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("upload", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_help___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("test", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_help___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("check-test", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_help___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lint", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_help___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("check-lint", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_help___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("clean", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_help___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("script", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_help___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("scripts", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_help___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("serve", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_help___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("env", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_help___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("exe", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_help___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("exec", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_help___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_help___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("translate-config", 16, 16);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_help(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lake_help___closed__1;
x_3 = lean_string_dec_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lake_help___closed__2;
x_5 = lean_string_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lake_help___closed__3;
x_7 = lean_string_dec_eq(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lake_help___closed__4;
x_9 = lean_string_dec_eq(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lake_help___closed__5;
x_11 = lean_string_dec_eq(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lake_help___closed__6;
x_13 = lean_string_dec_eq(x_1, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lake_help___closed__7;
x_15 = lean_string_dec_eq(x_1, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Lake_help___closed__8;
x_17 = lean_string_dec_eq(x_1, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Lake_help___closed__9;
x_19 = lean_string_dec_eq(x_1, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = l_Lake_help___closed__10;
x_21 = lean_string_dec_eq(x_1, x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = l_Lake_help___closed__11;
x_23 = lean_string_dec_eq(x_1, x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = l_Lake_help___closed__12;
x_25 = lean_string_dec_eq(x_1, x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = l_Lake_help___closed__13;
x_27 = lean_string_dec_eq(x_1, x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = l_Lake_help___closed__14;
x_29 = lean_string_dec_eq(x_1, x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = l_Lake_help___closed__15;
x_31 = lean_string_dec_eq(x_1, x_30);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = l_Lake_help___closed__16;
x_33 = lean_string_dec_eq(x_1, x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = l_Lake_helpScript___closed__2;
x_35 = lean_string_dec_eq(x_1, x_34);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = l_Lake_help___closed__17;
x_37 = lean_string_dec_eq(x_1, x_36);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = l_Lake_help___closed__18;
x_39 = lean_string_dec_eq(x_1, x_38);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = l_Lake_help___closed__19;
x_41 = lean_string_dec_eq(x_1, x_40);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = l_Lake_help___closed__20;
x_43 = lean_string_dec_eq(x_1, x_42);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = l_Lake_help___closed__21;
x_45 = lean_string_dec_eq(x_1, x_44);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = l_Lake_help___closed__22;
x_47 = lean_string_dec_eq(x_1, x_46);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = l_Lake_usage;
return x_48;
}
else
{
lean_object* x_49; 
x_49 = l_Lake_helpTranslateConfig;
return x_49;
}
}
else
{
lean_object* x_50; 
x_50 = l_Lake_helpLean;
return x_50;
}
}
else
{
lean_object* x_51; 
x_51 = l_Lake_helpExe;
return x_51;
}
}
else
{
lean_object* x_52; 
x_52 = l_Lake_helpExe;
return x_52;
}
}
else
{
lean_object* x_53; 
x_53 = l_Lake_helpEnv;
return x_53;
}
}
else
{
lean_object* x_54; 
x_54 = l_Lake_helpServe;
return x_54;
}
}
else
{
lean_object* x_55; 
x_55 = l_Lake_helpScriptRun;
return x_55;
}
}
else
{
lean_object* x_56; 
x_56 = l_Lake_helpScriptList;
return x_56;
}
}
else
{
lean_object* x_57; 
x_57 = l_Lake_helpScriptCli;
return x_57;
}
}
else
{
lean_object* x_58; 
x_58 = l_Lake_helpClean;
return x_58;
}
}
else
{
lean_object* x_59; 
x_59 = l_Lake_helpCheckLint;
return x_59;
}
}
else
{
lean_object* x_60; 
x_60 = l_Lake_helpLint;
return x_60;
}
}
else
{
lean_object* x_61; 
x_61 = l_Lake_helpCheckTest;
return x_61;
}
}
else
{
lean_object* x_62; 
x_62 = l_Lake_helpTest;
return x_62;
}
}
else
{
lean_object* x_63; 
x_63 = l_Lake_helpUpload;
return x_63;
}
}
else
{
lean_object* x_64; 
x_64 = l_Lake_helpUnpack;
return x_64;
}
}
else
{
lean_object* x_65; 
x_65 = l_Lake_helpPack;
return x_65;
}
}
else
{
lean_object* x_66; 
x_66 = l_Lake_helpUpdate;
return x_66;
}
}
else
{
lean_object* x_67; 
x_67 = l_Lake_helpUpdate;
return x_67;
}
}
else
{
lean_object* x_68; 
x_68 = l_Lake_helpCheckBuild;
return x_68;
}
}
else
{
lean_object* x_69; 
x_69 = l_Lake_helpBuild;
return x_69;
}
}
else
{
lean_object* x_70; 
x_70 = l_Lake_helpInit;
return x_70;
}
}
else
{
lean_object* x_71; 
x_71 = l_Lake_helpNew;
return x_71;
}
}
}
LEAN_EXPORT lean_object* l_Lake_help___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_help(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Version(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_CLI_Help(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Version(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_usage___closed__1 = _init_l_Lake_usage___closed__1();
lean_mark_persistent(l_Lake_usage___closed__1);
l_Lake_usage___closed__2 = _init_l_Lake_usage___closed__2();
lean_mark_persistent(l_Lake_usage___closed__2);
l_Lake_usage = _init_l_Lake_usage();
lean_mark_persistent(l_Lake_usage);
l_Lake_templateHelp___closed__1 = _init_l_Lake_templateHelp___closed__1();
lean_mark_persistent(l_Lake_templateHelp___closed__1);
l_Lake_templateHelp = _init_l_Lake_templateHelp();
lean_mark_persistent(l_Lake_templateHelp);
l_Lake_helpNew___closed__1 = _init_l_Lake_helpNew___closed__1();
lean_mark_persistent(l_Lake_helpNew___closed__1);
l_Lake_helpNew___closed__2 = _init_l_Lake_helpNew___closed__2();
lean_mark_persistent(l_Lake_helpNew___closed__2);
l_Lake_helpNew___closed__3 = _init_l_Lake_helpNew___closed__3();
lean_mark_persistent(l_Lake_helpNew___closed__3);
l_Lake_helpNew___closed__4 = _init_l_Lake_helpNew___closed__4();
lean_mark_persistent(l_Lake_helpNew___closed__4);
l_Lake_helpNew = _init_l_Lake_helpNew();
lean_mark_persistent(l_Lake_helpNew);
l_Lake_helpInit___closed__1 = _init_l_Lake_helpInit___closed__1();
lean_mark_persistent(l_Lake_helpInit___closed__1);
l_Lake_helpInit___closed__2 = _init_l_Lake_helpInit___closed__2();
lean_mark_persistent(l_Lake_helpInit___closed__2);
l_Lake_helpInit___closed__3 = _init_l_Lake_helpInit___closed__3();
lean_mark_persistent(l_Lake_helpInit___closed__3);
l_Lake_helpInit___closed__4 = _init_l_Lake_helpInit___closed__4();
lean_mark_persistent(l_Lake_helpInit___closed__4);
l_Lake_helpInit = _init_l_Lake_helpInit();
lean_mark_persistent(l_Lake_helpInit);
l_Lake_helpBuild___closed__1 = _init_l_Lake_helpBuild___closed__1();
lean_mark_persistent(l_Lake_helpBuild___closed__1);
l_Lake_helpBuild = _init_l_Lake_helpBuild();
lean_mark_persistent(l_Lake_helpBuild);
l_Lake_helpCheckBuild___closed__1 = _init_l_Lake_helpCheckBuild___closed__1();
lean_mark_persistent(l_Lake_helpCheckBuild___closed__1);
l_Lake_helpCheckBuild = _init_l_Lake_helpCheckBuild();
lean_mark_persistent(l_Lake_helpCheckBuild);
l_Lake_helpUpdate___closed__1 = _init_l_Lake_helpUpdate___closed__1();
lean_mark_persistent(l_Lake_helpUpdate___closed__1);
l_Lake_helpUpdate = _init_l_Lake_helpUpdate();
lean_mark_persistent(l_Lake_helpUpdate);
l_Lake_helpTest___closed__1 = _init_l_Lake_helpTest___closed__1();
lean_mark_persistent(l_Lake_helpTest___closed__1);
l_Lake_helpTest = _init_l_Lake_helpTest();
lean_mark_persistent(l_Lake_helpTest);
l_Lake_helpCheckTest___closed__1 = _init_l_Lake_helpCheckTest___closed__1();
lean_mark_persistent(l_Lake_helpCheckTest___closed__1);
l_Lake_helpCheckTest = _init_l_Lake_helpCheckTest();
lean_mark_persistent(l_Lake_helpCheckTest);
l_Lake_helpLint___closed__1 = _init_l_Lake_helpLint___closed__1();
lean_mark_persistent(l_Lake_helpLint___closed__1);
l_Lake_helpLint = _init_l_Lake_helpLint();
lean_mark_persistent(l_Lake_helpLint);
l_Lake_helpCheckLint___closed__1 = _init_l_Lake_helpCheckLint___closed__1();
lean_mark_persistent(l_Lake_helpCheckLint___closed__1);
l_Lake_helpCheckLint = _init_l_Lake_helpCheckLint();
lean_mark_persistent(l_Lake_helpCheckLint);
l_Lake_helpPack___closed__1 = _init_l_Lake_helpPack___closed__1();
lean_mark_persistent(l_Lake_helpPack___closed__1);
l_Lake_helpPack = _init_l_Lake_helpPack();
lean_mark_persistent(l_Lake_helpPack);
l_Lake_helpUnpack___closed__1 = _init_l_Lake_helpUnpack___closed__1();
lean_mark_persistent(l_Lake_helpUnpack___closed__1);
l_Lake_helpUnpack = _init_l_Lake_helpUnpack();
lean_mark_persistent(l_Lake_helpUnpack);
l_Lake_helpUpload___closed__1 = _init_l_Lake_helpUpload___closed__1();
lean_mark_persistent(l_Lake_helpUpload___closed__1);
l_Lake_helpUpload = _init_l_Lake_helpUpload();
lean_mark_persistent(l_Lake_helpUpload);
l_Lake_helpClean___closed__1 = _init_l_Lake_helpClean___closed__1();
lean_mark_persistent(l_Lake_helpClean___closed__1);
l_Lake_helpClean = _init_l_Lake_helpClean();
lean_mark_persistent(l_Lake_helpClean);
l_Lake_helpScriptCli___closed__1 = _init_l_Lake_helpScriptCli___closed__1();
lean_mark_persistent(l_Lake_helpScriptCli___closed__1);
l_Lake_helpScriptCli = _init_l_Lake_helpScriptCli();
lean_mark_persistent(l_Lake_helpScriptCli);
l_Lake_helpScriptList___closed__1 = _init_l_Lake_helpScriptList___closed__1();
lean_mark_persistent(l_Lake_helpScriptList___closed__1);
l_Lake_helpScriptList = _init_l_Lake_helpScriptList();
lean_mark_persistent(l_Lake_helpScriptList);
l_Lake_helpScriptRun___closed__1 = _init_l_Lake_helpScriptRun___closed__1();
lean_mark_persistent(l_Lake_helpScriptRun___closed__1);
l_Lake_helpScriptRun = _init_l_Lake_helpScriptRun();
lean_mark_persistent(l_Lake_helpScriptRun);
l_Lake_helpScriptDoc___closed__1 = _init_l_Lake_helpScriptDoc___closed__1();
lean_mark_persistent(l_Lake_helpScriptDoc___closed__1);
l_Lake_helpScriptDoc = _init_l_Lake_helpScriptDoc();
lean_mark_persistent(l_Lake_helpScriptDoc);
l_Lake_helpServe___closed__1 = _init_l_Lake_helpServe___closed__1();
lean_mark_persistent(l_Lake_helpServe___closed__1);
l_Lake_helpServe = _init_l_Lake_helpServe();
lean_mark_persistent(l_Lake_helpServe);
l_Lake_helpEnv___closed__1 = _init_l_Lake_helpEnv___closed__1();
lean_mark_persistent(l_Lake_helpEnv___closed__1);
l_Lake_helpEnv = _init_l_Lake_helpEnv();
lean_mark_persistent(l_Lake_helpEnv);
l_Lake_helpExe___closed__1 = _init_l_Lake_helpExe___closed__1();
lean_mark_persistent(l_Lake_helpExe___closed__1);
l_Lake_helpExe = _init_l_Lake_helpExe();
lean_mark_persistent(l_Lake_helpExe);
l_Lake_helpLean___closed__1 = _init_l_Lake_helpLean___closed__1();
lean_mark_persistent(l_Lake_helpLean___closed__1);
l_Lake_helpLean = _init_l_Lake_helpLean();
lean_mark_persistent(l_Lake_helpLean);
l_Lake_helpTranslateConfig___closed__1 = _init_l_Lake_helpTranslateConfig___closed__1();
lean_mark_persistent(l_Lake_helpTranslateConfig___closed__1);
l_Lake_helpTranslateConfig = _init_l_Lake_helpTranslateConfig();
lean_mark_persistent(l_Lake_helpTranslateConfig);
l_Lake_helpScript___closed__1 = _init_l_Lake_helpScript___closed__1();
lean_mark_persistent(l_Lake_helpScript___closed__1);
l_Lake_helpScript___closed__2 = _init_l_Lake_helpScript___closed__2();
lean_mark_persistent(l_Lake_helpScript___closed__2);
l_Lake_helpScript___closed__3 = _init_l_Lake_helpScript___closed__3();
lean_mark_persistent(l_Lake_helpScript___closed__3);
l_Lake_help___closed__1 = _init_l_Lake_help___closed__1();
lean_mark_persistent(l_Lake_help___closed__1);
l_Lake_help___closed__2 = _init_l_Lake_help___closed__2();
lean_mark_persistent(l_Lake_help___closed__2);
l_Lake_help___closed__3 = _init_l_Lake_help___closed__3();
lean_mark_persistent(l_Lake_help___closed__3);
l_Lake_help___closed__4 = _init_l_Lake_help___closed__4();
lean_mark_persistent(l_Lake_help___closed__4);
l_Lake_help___closed__5 = _init_l_Lake_help___closed__5();
lean_mark_persistent(l_Lake_help___closed__5);
l_Lake_help___closed__6 = _init_l_Lake_help___closed__6();
lean_mark_persistent(l_Lake_help___closed__6);
l_Lake_help___closed__7 = _init_l_Lake_help___closed__7();
lean_mark_persistent(l_Lake_help___closed__7);
l_Lake_help___closed__8 = _init_l_Lake_help___closed__8();
lean_mark_persistent(l_Lake_help___closed__8);
l_Lake_help___closed__9 = _init_l_Lake_help___closed__9();
lean_mark_persistent(l_Lake_help___closed__9);
l_Lake_help___closed__10 = _init_l_Lake_help___closed__10();
lean_mark_persistent(l_Lake_help___closed__10);
l_Lake_help___closed__11 = _init_l_Lake_help___closed__11();
lean_mark_persistent(l_Lake_help___closed__11);
l_Lake_help___closed__12 = _init_l_Lake_help___closed__12();
lean_mark_persistent(l_Lake_help___closed__12);
l_Lake_help___closed__13 = _init_l_Lake_help___closed__13();
lean_mark_persistent(l_Lake_help___closed__13);
l_Lake_help___closed__14 = _init_l_Lake_help___closed__14();
lean_mark_persistent(l_Lake_help___closed__14);
l_Lake_help___closed__15 = _init_l_Lake_help___closed__15();
lean_mark_persistent(l_Lake_help___closed__15);
l_Lake_help___closed__16 = _init_l_Lake_help___closed__16();
lean_mark_persistent(l_Lake_help___closed__16);
l_Lake_help___closed__17 = _init_l_Lake_help___closed__17();
lean_mark_persistent(l_Lake_help___closed__17);
l_Lake_help___closed__18 = _init_l_Lake_help___closed__18();
lean_mark_persistent(l_Lake_help___closed__18);
l_Lake_help___closed__19 = _init_l_Lake_help___closed__19();
lean_mark_persistent(l_Lake_help___closed__19);
l_Lake_help___closed__20 = _init_l_Lake_help___closed__20();
lean_mark_persistent(l_Lake_help___closed__20);
l_Lake_help___closed__21 = _init_l_Lake_help___closed__21();
lean_mark_persistent(l_Lake_help___closed__21);
l_Lake_help___closed__22 = _init_l_Lake_help___closed__22();
lean_mark_persistent(l_Lake_help___closed__22);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
