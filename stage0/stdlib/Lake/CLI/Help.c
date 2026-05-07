// Lean compiler output
// Module: Lake.CLI.Help
// Imports: public import Init.Data.ToString import Lake.Version
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
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lake_uiVersionString;
lean_object* lean_string_append(lean_object*, lean_object*);
static const lean_string_object l_Lake_usage___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3580, .m_capacity = 3580, .m_length = 3579, .m_data = "\n\nUSAGE:\n  lake [OPTIONS] <COMMAND>\n\nCOMMANDS:\n  new <name> <temp>     create a Lean package in a new directory\n  init <name> <temp>    create a Lean package in the current directory\n  build <targets>...    build targets\n  query <targets>...    build targets and output results\n  exe <exe> <args>...   build an exe and run it in Lake's environment\n  check-build           check if any default build targets are configured\n  test                  test the package using the configured test driver\n  check-test            check if there is a properly configured test driver\n  lint                  lint the package\n  check-lint            check if there is a properly configured lint driver\n  clean                 remove build outputs\n  shake                 minimize imports in source files\n  env <cmd> <args>...   execute a command in Lake's environment\n  lean <file>           elaborate a Lean file in Lake's context\n  update                update dependencies and save them to the manifest\n  pack                  pack build artifacts into an archive for distribution\n  unpack                unpack build artifacts from an distributed archive\n  upload <tag>          upload build artifacts to a GitHub release\n  cache                 manage the Lake cache\n  script                manage and run workspace scripts\n  scripts               shorthand for `lake script list`\n  run <script>          shorthand for `lake script run`\n  translate-config      change language of the package configuration\n  serve                 start the Lean language server\n\nBASIC OPTIONS:\n  --version             print version and exit\n  --help, -h            print help of the program or a command and exit\n  --dir, -d=file        use the package configuration in a specific directory\n  --file, -f=file       use a specific file for the package configuration\n  -K key[=value]        set the configuration file option named key\n  --old                 only rebuild modified modules (ignore transitive deps)\n  --rehash, -H          hash all files for traces (do not trust `.hash` files)\n  --update              update dependencies on load (e.g., before a build)\n  --packages=file       JSON file of package entries that override the manifest\n  --reconfigure, -R     elaborate configuration files instead of using OLeans\n  --keep-toolchain      do not update toolchain on workspace update\n  --allow-empty         accept bare builds with no default targets configured\n  --no-build            exit immediately if a build target is not up-to-date\n  --no-cache            build packages locally; do not download build caches\n  --try-cache           attempt to download build caches for supported packages\n  --json, -J            output JSON-formatted results (in `lake query`)\n  --text                output results as plain text (in `lake query`)\n\nOUTPUT OPTIONS:\n  --quiet, -q           hide informational logs and the progress indicator\n  --verbose, -v         show trace logs (command invocations) and built targets\n  --ansi, --no-ansi     toggle the use of ANSI escape codes to prettify output\n  --log-level=lv        minimum log level to output on success\n                        (levels: trace, info, warning, error)\n  --fail-level=lv       minimum log level to fail a build (default: error)\n  --iofail              fail build if any I/O or other info is logged\n                        (same as --fail-level=info)\n  --wfail               fail build if warnings are logged\n                        (same as --fail-level=warning)\n\n\nSee `lake help <command>` for more information on a specific command."};
static const lean_object* l_Lake_usage___closed__0 = (const lean_object*)&l_Lake_usage___closed__0_value;
static lean_once_cell_t l_Lake_usage___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_usage___closed__1;
LEAN_EXPORT lean_object* l_Lake_usage;
static const lean_string_object l___private_Lake_CLI_Help_0__Lake_newInitHelp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 627, .m_capacity = 627, .m_length = 626, .m_data = "If you are using Lake through Elan (which is standard), you can create a\npackage with a specific Lean version via the `+` option.\n\nThe initial configuration and starter files are based on the template:\n\n  std                   library and executable; default\n  exe                   executable only\n  lib                   library only\n  math-lax              library only with a Mathlib dependency\n  math                  library with Mathlib standards for linting and workflows\n\nTemplates can be suffixed with `.lean` or `.toml` to produce a Lean or TOML\nversion of the configuration file, respectively. The default is TOML."};
static const lean_object* l___private_Lake_CLI_Help_0__Lake_newInitHelp___closed__0 = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_newInitHelp___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Help_0__Lake_newInitHelp = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_newInitHelp___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Help_0__Lake_helpNew___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 739, .m_capacity = 739, .m_length = 738, .m_data = "Create a Lean package in a new directory\n\nUSAGE:\n  lake [+<lean-version>] new <name> [<template>][.<language>]\n\nIf you are using Lake through Elan (which is standard), you can create a\npackage with a specific Lean version via the `+` option.\n\nThe initial configuration and starter files are based on the template:\n\n  std                   library and executable; default\n  exe                   executable only\n  lib                   library only\n  math-lax              library only with a Mathlib dependency\n  math                  library with Mathlib standards for linting and workflows\n\nTemplates can be suffixed with `.lean` or `.toml` to produce a Lean or TOML\nversion of the configuration file, respectively. The default is TOML."};
static const lean_object* l___private_Lake_CLI_Help_0__Lake_helpNew___closed__0 = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpNew___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Help_0__Lake_helpNew = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpNew___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Help_0__Lake_helpInit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 845, .m_capacity = 845, .m_length = 844, .m_data = "Create a Lean package in the current directory\n\nUSAGE:\n  lake [+<lean-version>] init [<name>] [<template>][.<language>]\n\nIf you are using Lake through Elan (which is standard), you can create a\npackage with a specific Lean version via the `+` option.\n\nThe initial configuration and starter files are based on the template:\n\n  std                   library and executable; default\n  exe                   executable only\n  lib                   library only\n  math-lax              library only with a Mathlib dependency\n  math                  library with Mathlib standards for linting and workflows\n\nTemplates can be suffixed with `.lean` or `.toml` to produce a Lean or TOML\nversion of the configuration file, respectively. The default is TOML.\n\nYou can create a package with current directory's name via `lake init .`\nor a bare `lake init`."};
static const lean_object* l___private_Lake_CLI_Help_0__Lake_helpInit___closed__0 = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpInit___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Help_0__Lake_helpInit = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpInit___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Help_0__Lake_helpBuild___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2435, .m_capacity = 2435, .m_length = 2434, .m_data = "Build targets\n\nUSAGE:\n  lake build [<targets>...] [-o <mappings>]\n\nA target is specified with a string of the form:\n\n  [@[<package>]/][<target>|[+]<module>][:<facet>]\n\nYou can also use the source path of a module as a target. For example,\n\n  lake build Foo/Bar.lean:o\n\nwill build the Lean module (within the workspace) whose source file is\n`Foo/Bar.lean` and compile the generated C file into a native object file.\n\nThe `@` and `+` markers can be used to disambiguate packages and modules\nfrom file paths or other kinds of targets (e.g., executables or libraries).\n\nLIBRARY FACETS:         build the library's ...\n  leanArts (default)    Lean artifacts (*.olean, *.ilean, *.c files)\n  static                static artifact (*.a file)\n  shared                shared artifact (*.so, *.dll, or *.dylib file)\n\nMODULE FACETS:          build the module's ...\n  deps                  dependencies (e.g., imports, shared libraries, etc.)\n  leanArts (default)    Lean artifacts (*.olean, *.ilean, *.c files)\n  olean                 OLean (binary blob of Lean data for importers)\n  ilean                 ILean (binary blob of metadata for the Lean LSP server)\n  c                     compiled C file\n  bc                    compiled LLVM bitcode file\n  c.o                   compiled object file (of its C file)\n  bc.o                  compiled object file (of its LLVM bitcode file)\n  o                     compiled object file (of its configured backend)\n  dynlib                shared library (e.g., for `--load-dynlib`)\n\nTARGET EXAMPLES:        build the ...\n  a                     default facet(s) of target `a`\n  @a                    default target(s) of package `a`\n  +A                    default facet(s) of module `A`\n  @/a                   default facet(s) of target `a` of the root package\n  @a/b                  default facet(s) of target `b` of package `a`\n  @a/+A:c               C file of module `A` of package `a`\n  :foo                  facet `foo` of the root package\n\nA bare `lake build` command will build the default target(s) of the root\npackage. Package dependencies are not updated during a build.\n\nWith the Lake cache enabled, the `-o` option will cause Lake to track the\ninput-to-outputs mappings of targets in the root package touched during the\nbuild and write them to the specified file at the end of the build. These\nmappings can then be used to upload build artifacts to a remote cache with\n`lake cache put`."};
static const lean_object* l___private_Lake_CLI_Help_0__Lake_helpBuild___closed__0 = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpBuild___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Help_0__Lake_helpBuild = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpBuild___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Help_0__Lake_helpQuery___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 512, .m_capacity = 512, .m_length = 511, .m_data = "Build targets and output results\n\nUSAGE:\n  lake query [<targets>...]\n\nBuilds a set of targets, reporting progress on standard error and outputting\nthe results on standard out. Target results are output in the same order they\nare listed and end with a newline. If `--json` is set, results are formatted as\nJSON. Otherwise, they are printed as raw strings. Targets which do not have\noutput configured will be printed as an empty string or `null`.\n\nSee `lake help build` for information on and examples of targets."};
static const lean_object* l___private_Lake_CLI_Help_0__Lake_helpQuery___closed__0 = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpQuery___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Help_0__Lake_helpQuery = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpQuery___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Help_0__Lake_helpCheckBuild___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 305, .m_capacity = 305, .m_length = 304, .m_data = "Check if any default build targets are configured\n\nUSAGE:\n  lake check-build\n\nExits with code 0 if the workspace's root package has any\ndefault targets configured. Errors (with code 1) otherwise.\n\nDoes NOT verify that the configured default targets are valid.\nIt merely verifies that some are specified.\n"};
static const lean_object* l___private_Lake_CLI_Help_0__Lake_helpCheckBuild___closed__0 = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpCheckBuild___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Help_0__Lake_helpCheckBuild = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpCheckBuild___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Help_0__Lake_helpUpdate___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 713, .m_capacity = 713, .m_length = 712, .m_data = "Update dependencies and save them to the manifest\n\nUSAGE:\n  lake update [<package>...]\n\nALIAS: lake upgrade\n\nUpdates the Lake package manifest (i.e., `lake-manifest.json`),\ndownloading and upgrading packages as needed. For each new (transitive) git\ndependency, the appropriate commit is cloned into a subdirectory of\n`packagesDir`. No copy is made of local dependencies.\n\nIf a set of packages are specified, said dependencies are upgraded to\nthe latest version compatible with the package's configuration (or removed if\nremoved from the configuration). If there are dependencies on multiple versions\nof the same package, the version materialized is undefined.\n\nA bare `lake update` will upgrade all dependencies."};
static const lean_object* l___private_Lake_CLI_Help_0__Lake_helpUpdate___closed__0 = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpUpdate___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Help_0__Lake_helpUpdate = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpUpdate___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Help_0__Lake_helpTest___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 617, .m_capacity = 617, .m_length = 616, .m_data = "Test the workspace's root package using its configured test driver\n\nUSAGE:\n  lake test [-- <args>...]\n\nA test driver can be configured by either setting the 'testDriver'\npackage configuration option or by tagging a script, executable, or library\n`@[test_driver]`. A definition in a dependency can be used as a test driver\nby using the `<pkg>/<name>` syntax for the 'testDriver' configuration option.\n\nA script test driver will be run with the  package configuration's\n`testDriverArgs` plus the CLI `args`. An executable test driver will be\nbuilt and then run like a script. A library test driver will just be built.\n"};
static const lean_object* l___private_Lake_CLI_Help_0__Lake_helpTest___closed__0 = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpTest___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Help_0__Lake_helpTest = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpTest___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Help_0__Lake_helpCheckTest___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 344, .m_capacity = 344, .m_length = 343, .m_data = "Check if there is a properly configured test driver\n\nUSAGE:\n  lake check-test\n\nExits with code 0 if the workspace's root package has a properly\nconfigured lint driver. Errors (with code 1) otherwise.\n\nDoes NOT verify that the configured test driver actually exists in the\npackage or its dependencies. It merely verifies that one is specified.\n"};
static const lean_object* l___private_Lake_CLI_Help_0__Lake_helpCheckTest___closed__0 = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpCheckTest___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Help_0__Lake_helpCheckTest = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpCheckTest___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Help_0__Lake_helpLint___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1681, .m_capacity = 1681, .m_length = 1680, .m_data = "Lint the workspace's root package\n\nUSAGE:\n  lake lint [OPTIONS] [<MODULE>...] [-- <args>...]\n\nBy default, runs the package's configured lint driver. If `builtinLint` is\nset to `true` in the package configuration, builtin lints also run.\n\nBuiltin linting (`--builtin-lint`, `--builtin-only`, `--clippy`, `--lint-all`,\n`--lint-only`, or `builtinLint = true` in the package configuration) drives a\nbuild of the targeted modules with the requested linter options enabled.\nThe lint driver path on its own does not trigger a build.\n\nPositional `MODULE` arguments narrow only the builtin lints; if omitted,\nthe workspace's default target roots are used. The lint driver is invoked\nwith `lintDriverArgs` from the package config plus any arguments after\n`--`; the `MODULE` list is not passed to it.\n\nOPTIONS:\n  --builtin-lint        run builtin environment and text linters\n  --builtin-only        run only builtin linters, skip the lint driver\n  --clippy              run only non-default (clippy) builtin linters\n  --lint-all            run all registered linters, including defaults, clippy,\n                        and any other disabled-by-default linters\n  --lint-only <name>    run only the specified linter (repeatable)\n\nA lint driver can be configured by either setting the `lintDriver` package\nconfiguration option or by tagging a script or executable `@[lint_driver]`.\nA definition in a dependency can be used as a lint driver by using the\n`<pkg>/<name>` syntax for the 'lintDriver' configuration option.\n\nA script lint driver will be run with the package configuration's\n`lintDriverArgs` plus the CLI `args`. An executable lint driver will be\nbuilt and then run like a script.\n"};
static const lean_object* l___private_Lake_CLI_Help_0__Lake_helpLint___closed__0 = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpLint___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Help_0__Lake_helpLint = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpLint___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Help_0__Lake_helpCheckLint___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 344, .m_capacity = 344, .m_length = 343, .m_data = "Check if there is a properly configured lint driver\n\nUSAGE:\n  lake check-lint\n\nExits with code 0 if the workspace's root package has a properly\nconfigured lint driver. Errors (with code 1) otherwise.\n\nDoes NOT verify that the configured lint driver actually exists in the\npackage or its dependencies. It merely verifies that one is specified.\n"};
static const lean_object* l___private_Lake_CLI_Help_0__Lake_helpCheckLint___closed__0 = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpCheckLint___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Help_0__Lake_helpCheckLint = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpCheckLint___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Help_0__Lake_helpPack___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 377, .m_capacity = 377, .m_length = 376, .m_data = "Pack build artifacts into an archive for distribution\n\nUSAGE:\n  lake pack [<file.tgz>]\n\nPacks the root package's `buildDir` into a gzip tar archive using `tar`.\nIf a path for the archive is not specified, creates an archive in the package's\nLake directory (`.lake`) named according to its `buildArchive` setting.\n\nDoes NOT build any artifacts. It just packs the existing ones."};
static const lean_object* l___private_Lake_CLI_Help_0__Lake_helpPack___closed__0 = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpPack___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Help_0__Lake_helpPack = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpPack___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Help_0__Lake_helpUnpack___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 297, .m_capacity = 297, .m_length = 296, .m_data = "Unpack build artifacts from a distributed archive\n\nUSAGE:\n  lake unpack [<file.tgz>]\n\nUnpack build artifacts from the gzip tar archive `file.tgz` into the root\npackage's `buildDir`. If a path for the archive is not specified, uses the\nthe package's `buildArchive` in its Lake directory (`.lake`)."};
static const lean_object* l___private_Lake_CLI_Help_0__Lake_helpUnpack___closed__0 = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpUnpack___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Help_0__Lake_helpUnpack = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpUnpack___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Help_0__Lake_helpUpload___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 224, .m_capacity = 224, .m_length = 223, .m_data = "Upload build artifacts to a GitHub release\n\nUSAGE:\n  lake upload <tag>\n\nPacks the root package's `buildDir` into a `tar.gz` archive using `tar` and\nthen uploads the asset to the pre-existing GitHub release `tag` using `gh`."};
static const lean_object* l___private_Lake_CLI_Help_0__Lake_helpUpload___closed__0 = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpUpload___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Help_0__Lake_helpUpload = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpUpload___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Help_0__Lake_helpClean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 208, .m_capacity = 208, .m_length = 207, .m_data = "Remove build outputs\n\nUSAGE:\n  lake clean [<package>...]\n\nIf no package is specified, deletes the build directories of every package in\nthe workspace. Otherwise, just deletes those of the specified packages."};
static const lean_object* l___private_Lake_CLI_Help_0__Lake_helpClean___closed__0 = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpClean___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Help_0__Lake_helpClean = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpClean___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Help_0__Lake_helpShake___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1473, .m_capacity = 1473, .m_length = 1472, .m_data = "Minimize imports in Lean source files\n\nUSAGE:\n  lake shake [OPTIONS] [<MODULE>...]\n\nChecks the current project for unused imports by analyzing generated `.olean`\nfiles to deduce required imports and ensuring that every import contributes\nsome constant or other elaboration dependency.\n\nARGUMENTS:\n  <MODULE>              A module path like `Mathlib`. All files transitively\n                        reachable from the provided module(s) will be checked.\n                        If not specified, uses the package's default targets.\n\nOPTIONS:\n  --force               Skip the `lake build --no-build` sanity check\n  --keep-implied        Preserve imports implied by other imports\n  --keep-prefix         Prefer parent module imports over specific submodules\n  --keep-public         Preserve all `public` imports for API stability\n  --add-public          Add new imports as `public` if they were in the\n                        original public closure\n  --explain             Show which constants require each import\n  --fix                 Apply suggested fixes directly to source files\n  --gh-style            Output in GitHub problem matcher format\n\nANNOTATIONS:\n  Source files can contain special comments to control shake behavior:\n\n  * `module -- shake: keep-downstream`\n    Preserves this module in all downstream modules\n\n  * `module -- shake: keep-all`\n    Preserves all existing imports in this module\n\n  * `import X -- shake: keep`\n    Preserves this specific import"};
static const lean_object* l___private_Lake_CLI_Help_0__Lake_helpShake___closed__0 = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpShake___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Help_0__Lake_helpShake = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpShake___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Help_0__Lake_helpCacheCli___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 704, .m_capacity = 704, .m_length = 703, .m_data = "Manage the Lake cache\n\nUSAGE:\n  lake cache <COMMAND>\n\nCOMMANDS:\n  get [<mappings>]      download build outputs into the local Lake cache\n  put <mappings>        upload build outputs to a remote cache\n  add <mappings>        add input-to-output mappings to the Lake cache\n  clean                 removes ALL from the local Lake cache\n  services              print configured remote cache services\n\nSTAGING COMMANDS:\n  stage <map> <dir>     copy build outputs from the cache to a directory\n  unstage <dir>         cache build outputs from a staging directory\n  put-staged <dir>      upload build outputs from a staging directory\n\nSee `lake cache help <command>` for more information on a specific command."};
static const lean_object* l___private_Lake_CLI_Help_0__Lake_helpCacheCli___closed__0 = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpCacheCli___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Help_0__Lake_helpCacheCli = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpCacheCli___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Help_0__Lake_helpCacheGet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2912, .m_capacity = 2912, .m_length = 2911, .m_data = "Download build outputs from a remote service into the Lake cache\n\nUSAGE:\n  lake cache get [<mappings>]\n\nOPTIONS:\n  --max-revs=<n>                  backtrack up to n revisions (default: 100)\n  --rev=<commit-hash>             uses this exact revision to lookup artifacts\n  --service=<name>                cache service to fetch from\n  --repo=<github-repo>            GitHub repository of the package or a fork\n  --platform=<target-triple>      with Reservoir or --repo, sets the platform\n  --toolchain=<name>              with Reservoir or --repo, sets the toolchain\n  --scope=<remote-scope>          scope for a custom endpoint\n  --mappings-only                 only download mappings, delay artifacts\n  --force-download                redownload existing files\n\nDownloads build outputs for packages in the workspace from a remote cache\nservice. The cache service used can be specified via the `--service` option.\nOtherwise, Lake will the system default, or, if none is configured, Reservoir.\nSee `lake cache services` for more information on how to configure services.\n\nIf an input-to-outputs mappings file, `--scope`, or `--repo` is provided,\nLake will download build outputs for the root package. Otherwise, it will use\nReservoir to download outputs for each dependency in the workspace (in order).\nNon-Reservoir dependencies will be skipped.\n\nTo determine what to download, Lake searches for input-to-output mappings for\na given build of the package via the cache service. This mapping is identified\nby a Git revision and prefixed with a scope derived from the package's name,\nGitHub repository, Lean toolchain, and current platform. The exact configuration\ncan be customized using options.\n\nFor Reservoir, setting `--repo` will cause Lake to lookup outputs for the root\npackage by a repository name, rather than the package's. This can be used to\ndownload outputs for a fork of the Reservoir package (if such artifacts are\navailable). The `--platform` and `--toolchain` options can be used to download\nartifacts for a different platform/toolchain configuration than Lake detects.\nFor a custom endpoint, the full prefix Lake uses can be set via  `--scope`.\n\nIf `--rev` is not set, Lake uses the package's current revision to lookup\nartifacts. If no mappings are found, Lake will backtrack the Git history up to\n`--max-revs`, looking for a revision with mappings. If `--max-revs` is 0, Lake\nwill search the repository's entire history (or as far as Git will allow).\n\nBy default, Lake will download both the input-to-output mappings and the\noutput artifacts for a package. By using `--mappings-onlys`, Lake will only\ndownload the mappings and delay downloading artifacts until they are needed.\n\nIf a download for an artifact fails or the download process for a whole\npackage fails, Lake will report this and continue on to the next. Once done,\nif any download failed, Lake will exit with a nonzero status code."};
static const lean_object* l___private_Lake_CLI_Help_0__Lake_helpCacheGet___closed__0 = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpCacheGet___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Help_0__Lake_helpCacheGet = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpCacheGet___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Help_0__Lake_helpCachePut___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1824, .m_capacity = 1824, .m_length = 1823, .m_data = "Upload build outputs from the Lake cache to a remote service\n\nUSAGE:\n  lake cache put <mappings> <scope-option>\n\nUploads the input-to-output mappings contained in the specified file along\nwith the corresponding output artifacts to a remote cache. The cache service\nused can be specified via the `--service` option. If not specified, Lake will use\nthe system default, or error if none is configured. See the help page of\n`lake cache services` for more information on how to configure services.\n\nFiles are uploaded using the AWS Signature Version 4 authentication protocol\nvia `curl`. Thus, the service should generally be an S3-compatible bucket. The\nauthentication key is set via the `LAKE_CACHE_KEY` environment variable.\n\nSince Lake does not currently use cryptographically secure hashes for\nartifacts and outputs, uploads to the cache are prefixed with a scope to avoid\nclashes. This scope is configured with the following options:\n\n  --scope=<remote-scope>          sets a fixed scope\n  --repo=<github-repo>            uses the repository + toolchain & platform\n  --toolchain=<name>              with --repo, sets the toolchain\n  --platform=<target-triple>      with --repo, sets the platform\n\nAt least one of `--scope` or `--repo` must be set. If `--repo` is used, Lake\nwill produce a scope by augmenting the repository with toolchain and platform\ninformation as it deems necessary. If `--scope` is set, Lake will use the\nspecified scope verbatim.\n\nArtifacts are uploaded to the artifact endpoint with a file name derived\nfrom their Lake content hash (and prefixed by the repository or scope).\nThe mappings file is uploaded to the revision endpoint with a file name\nderived from the package's current Git revision (and prefixed by the\nfull scope). As such, the command will warn if the work tree currently\nhas changes."};
static const lean_object* l___private_Lake_CLI_Help_0__Lake_helpCachePut___closed__0 = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpCachePut___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Help_0__Lake_helpCachePut = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpCachePut___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Help_0__Lake_helpCacheAdd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1008, .m_capacity = 1008, .m_length = 1007, .m_data = "Add input-to-output mappings to the Lake cache\n\nUSAGE:\n  lake cache add <mappings>\n\nOPTIONS:\n  --service=<name>                cache service to fetch from on demand\n  --scope=<remote-scope>          the prefix of artifacts within the service\n  --repo=<github-repo>            for Reservoir, a GitHub repository scope\n\nReads a list of input-to-output mappings from the provided file and adds\nthem to the local Lake cache. If `--service` is provided, the output artifacts\ncan then be fetched lazily from that service during a Lake build. The service\nmust either be `reservoir` or  be configured through the Lake system\nconfiguration (see the help page of `lake cache services` for details).\n\nSince Lake does not currently use cryptographically secure hashes for\nartifacts and outputs, artifacts in a cache service are prefixed with a scope\nto avoid clashes. For Reservoir, this scope can either be a package (set via\n`--scope`) or a repository (set via `--repo`). For S3 services, both options\nare synonymous."};
static const lean_object* l___private_Lake_CLI_Help_0__Lake_helpCacheAdd___closed__0 = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpCacheAdd___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Help_0__Lake_helpCacheAdd = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpCacheAdd___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Help_0__Lake_helpCacheStage___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 359, .m_capacity = 359, .m_length = 358, .m_data = "Copy build outputs from the cache to a staging directory\n\nUSAGE:\n  lake cache stage <mappings> <staging-directory>\n\nCreates the staging directory and copies the mappings file to it. Then, it\ncopies all artifacts described within the mappings file from the cache to the\nstaging directory. Errors if any of the artifacts described cannot be found in\nthe cache."};
static const lean_object* l___private_Lake_CLI_Help_0__Lake_helpCacheStage___closed__0 = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpCacheStage___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Help_0__Lake_helpCacheStage = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpCacheStage___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Help_0__Lake_helpCacheUnstage___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 416, .m_capacity = 416, .m_length = 415, .m_data = "Cache build outputs from a staging directory\n\nUSAGE:\n  lake cache unstage <staging-directory>\n\nCopies the mappings and artifacts stored in staging directory (e.g., via\n`lake cache stage`) back into the cache.\n\nReads the mappings file located at `outputs.jsonl` within the staging\ndirectory and writes the mappings to the Lake cache. Then, it copies the\ndescribed artifacts from the staging directory into the cache."};
static const lean_object* l___private_Lake_CLI_Help_0__Lake_helpCacheUnstage___closed__0 = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpCacheUnstage___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Help_0__Lake_helpCacheUnstage = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpCacheUnstage___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Help_0__Lake_helpCachePutStaged___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 757, .m_capacity = 757, .m_length = 756, .m_data = "Upload build outputs from a staging directory to a remote service\n\nUSAGE:\n  lake cache put-staged <staging-directory>\n\nOPTIONS:\n  --scope=<remote-scope>          verbatim scope\n  --repo=<github-repo>            scope with repository + toolchain & platform\n  --toolchain=<name>              with --repo, sets the toolchain\n  --platform=<target-triple>      with --repo, sets the platform\n\nWorks like `lake cache put` but uploads outputs from the staging directory\ninstead of the Lake cache. Does not configure the workspace and thus does not\nexecute arbitrary user code. However, because of this, the package's platform\nand toolchain settings will not be automatically detected and must be\nspecified manually via `--platform` and `--toolchain` (if desired)."};
static const lean_object* l___private_Lake_CLI_Help_0__Lake_helpCachePutStaged___closed__0 = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpCachePutStaged___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Help_0__Lake_helpCachePutStaged = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpCachePutStaged___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Help_0__Lake_helpCacheClean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 275, .m_capacity = 275, .m_length = 274, .m_data = "Removes ALL files from the local Lake cache\n\nUSAGE:\n  lake cache clean\n\nDeletes the configured Lake cache directory. If a workspace configuration\nexists, this will delete the cache directory it uses. Otherwise, it will\ndelete the default Lake cache directory for the system."};
static const lean_object* l___private_Lake_CLI_Help_0__Lake_helpCacheClean___closed__0 = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpCacheClean___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Help_0__Lake_helpCacheClean = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpCacheClean___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Help_0__Lake_helpCacheServices___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 749, .m_capacity = 749, .m_length = 748, .m_data = "Print configured remote cache services\n\nUSAGE:\n  lake cache services\n\nPrints the name of each configured remote cache services (one per line).\nAdditional services can be added by modifying the system Lake configuration.\nThe exact location of the this configuration file is system dependent and can\nbe set by `LAKE_CONFIG`, but it is usually located at `~/.lake/config.toml`.\n\nThe configuration of the system cache could look something like the following:\n\n  cache.defaultService = \"my-s3\"\n  cache.defaultUploadService = \"my-s3\"\n\n  [[cache.service]]\n  name = \"my-s3\"\n  kind = \"s3\"\n  artifactEndpoint = \"https://my-s3.com/a0\"\n  revisionEndpoint = \"https://my-s3.com/r0\"\n\nIf no `cache.defaultService` is configured, Lake will use Reservoir by default."};
static const lean_object* l___private_Lake_CLI_Help_0__Lake_helpCacheServices___closed__0 = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpCacheServices___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Help_0__Lake_helpCacheServices = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpCacheServices___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Help_0__Lake_helpScriptCli___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 287, .m_capacity = 287, .m_length = 286, .m_data = "Manage Lake scripts\n\nUSAGE:\n  lake script <COMMAND>\n\nCOMMANDS:\n  list                  list available scripts\n  run <script>          run a script\n  doc <script>          print the docstring of a given script\n\nSee `lake script help <command>` for more information on a specific command."};
static const lean_object* l___private_Lake_CLI_Help_0__Lake_helpScriptCli___closed__0 = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpScriptCli___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Help_0__Lake_helpScriptCli = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpScriptCli___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Help_0__Lake_helpScriptList___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 144, .m_capacity = 144, .m_length = 143, .m_data = "List available scripts\n\nUSAGE:\n  lake script list\n\nALIAS: lake scripts\n\nThis command prints the list of all available scripts in the workspace."};
static const lean_object* l___private_Lake_CLI_Help_0__Lake_helpScriptList___closed__0 = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpScriptList___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Help_0__Lake_helpScriptList = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpScriptList___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Help_0__Lake_helpScriptRun___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 290, .m_capacity = 290, .m_length = 289, .m_data = "Run a script\n\nUSAGE:\n  lake script run [[<package>/]<script>] [<args>...]\n\nALIAS: lake run\n\nThis command runs the `script` of the workspace (or the specific `package`),\npassing `args` to it.\n\nA bare `lake run` command will run the default script(s) of the root package\n(with no arguments)."};
static const lean_object* l___private_Lake_CLI_Help_0__Lake_helpScriptRun___closed__0 = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpScriptRun___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Help_0__Lake_helpScriptRun = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpScriptRun___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Help_0__Lake_helpScriptDoc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 151, .m_capacity = 151, .m_length = 150, .m_data = "Print a script's docstring\n\nUSAGE:\n  lake script doc [<package>/]<script>\n\nPrint the docstring of `script` in the workspace or the specific `package`."};
static const lean_object* l___private_Lake_CLI_Help_0__Lake_helpScriptDoc___closed__0 = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpScriptDoc___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Help_0__Lake_helpScriptDoc = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpScriptDoc___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Help_0__Lake_helpServe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 214, .m_capacity = 214, .m_length = 213, .m_data = "Start the Lean language server\n\nUSAGE:\n  lake serve [-- <args>...]\n\nRun the language server of the Lean installation (i.e., via `lean --server`)\nwith the package configuration's `moreServerArgs` field and `args`.\n"};
static const lean_object* l___private_Lake_CLI_Help_0__Lake_helpServe___closed__0 = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpServe___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Help_0__Lake_helpServe = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpServe___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Help_0__Lake_helpEnv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1235, .m_capacity = 1235, .m_length = 1234, .m_data = "Execute a command in Lake's environment\n\nUSAGE:\n  lake env [<cmd>] [<args>...]\n\nSpawns a new process executing `cmd` with the given `args` and with\nthe environment set based on the detected Lean/Lake installations and\nthe workspace configuration (if it exists).\n\nSpecifically, this command sets the following environment variables:\n\n  LAKE                  set to the detected Lake executable\n  LAKE_HOME             set to the detected Lake home\n  LEAN_SYSROOT          set to the detected Lean toolchain directory\n  LEAN_AR               set to the detected Lean `ar` binary\n  LEAN_CC               set to the detected `cc` (if not using the bundled one)\n  LEAN_PATH             adds Lake's and the workspace's Lean library dirs\n  LEAN_SRC_PATH         adds Lake's and the workspace's source dirs\n  PATH                  adds Lean's, Lake's, and the workspace's binary dirs\n  PATH                  adds Lean's and the workspace's library dirs (Windows)\n  DYLD_LIBRARY_PATH     adds Lean's and the workspace's library dirs (MacOS)\n  LD_LIBRARY_PATH       adds Lean's and the workspace's library dirs (other)\n\nA bare `lake env` will print out the variables set and their values,\nusing the form NAME=VALUE like the POSIX `env` command."};
static const lean_object* l___private_Lake_CLI_Help_0__Lake_helpEnv___closed__0 = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpEnv___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Help_0__Lake_helpEnv = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpEnv___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Help_0__Lake_helpExe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 379, .m_capacity = 379, .m_length = 378, .m_data = "Build an executable target and run it in Lake's environment\n\nUSAGE:\n  lake exe <exe-target> [<args>...]\n\nALIAS: lake exec\n\nLooks for the executable target in the workspace (see `lake help build` to\nlearn how to specify targets), builds it if it is out of date, and then runs\nit with the given `args` in Lake's environment (see `lake help env` for how\nthe environment is set up)."};
static const lean_object* l___private_Lake_CLI_Help_0__Lake_helpExe___closed__0 = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpExe___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Help_0__Lake_helpExe = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpExe___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Help_0__Lake_helpLean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 395, .m_capacity = 395, .m_length = 394, .m_data = "Elaborate a Lean file in the context of the Lake workspace\n\nUSAGE:\n  lake lean <file> [-- <args>...]\n\nBuild the imports of the given file and then runs `lean` on it using\nthe workspace's root package's additional Lean arguments and the given args\n(in that order). The `lean` process is executed in Lake's environment like\n`lake env lean` (see `lake help env` for how the environment is set up)."};
static const lean_object* l___private_Lake_CLI_Help_0__Lake_helpLean___closed__0 = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpLean___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Help_0__Lake_helpLean = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpLean___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Help_0__Lake_helpTranslateConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 557, .m_capacity = 557, .m_length = 556, .m_data = "Translate a Lake configuration file into a different language\n\nUSAGE:\n  lake translate-config <lang> [<out-file>]\n\nTranslates the loaded package's configuration into another of\nLake's supported configuration languages (i.e., either `lean` or `toml`).\nThe produced file is written to `out-file` or, if not provided, the path of\nthe configuration file with the new language's extension. If the output file\nalready exists, Lake will error.\n\nTranslation is lossy. It does not preserve comments or formatting and\nnon-declarative configuration will be discarded."};
static const lean_object* l___private_Lake_CLI_Help_0__Lake_helpTranslateConfig___closed__0 = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpTranslateConfig___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Help_0__Lake_helpTranslateConfig = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpTranslateConfig___closed__0_value;
static const lean_string_object l_Lake_helpScript___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "list"};
static const lean_object* l_Lake_helpScript___closed__0 = (const lean_object*)&l_Lake_helpScript___closed__0_value;
static const lean_string_object l_Lake_helpScript___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "run"};
static const lean_object* l_Lake_helpScript___closed__1 = (const lean_object*)&l_Lake_helpScript___closed__1_value;
static const lean_string_object l_Lake_helpScript___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "doc"};
static const lean_object* l_Lake_helpScript___closed__2 = (const lean_object*)&l_Lake_helpScript___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_helpScript(lean_object*);
LEAN_EXPORT lean_object* l_Lake_helpScript___boxed(lean_object*);
static const lean_string_object l_Lake_helpCache___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "get"};
static const lean_object* l_Lake_helpCache___closed__0 = (const lean_object*)&l_Lake_helpCache___closed__0_value;
static const lean_string_object l_Lake_helpCache___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "put"};
static const lean_object* l_Lake_helpCache___closed__1 = (const lean_object*)&l_Lake_helpCache___closed__1_value;
static const lean_string_object l_Lake_helpCache___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "add"};
static const lean_object* l_Lake_helpCache___closed__2 = (const lean_object*)&l_Lake_helpCache___closed__2_value;
static const lean_string_object l_Lake_helpCache___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "stage"};
static const lean_object* l_Lake_helpCache___closed__3 = (const lean_object*)&l_Lake_helpCache___closed__3_value;
static const lean_string_object l_Lake_helpCache___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "unstage"};
static const lean_object* l_Lake_helpCache___closed__4 = (const lean_object*)&l_Lake_helpCache___closed__4_value;
static const lean_string_object l_Lake_helpCache___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "put-staged"};
static const lean_object* l_Lake_helpCache___closed__5 = (const lean_object*)&l_Lake_helpCache___closed__5_value;
static const lean_string_object l_Lake_helpCache___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "clean"};
static const lean_object* l_Lake_helpCache___closed__6 = (const lean_object*)&l_Lake_helpCache___closed__6_value;
static const lean_string_object l_Lake_helpCache___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "services"};
static const lean_object* l_Lake_helpCache___closed__7 = (const lean_object*)&l_Lake_helpCache___closed__7_value;
LEAN_EXPORT lean_object* l_Lake_helpCache(lean_object*);
LEAN_EXPORT lean_object* l_Lake_helpCache___boxed(lean_object*);
static const lean_string_object l_Lake_help___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "new"};
static const lean_object* l_Lake_help___closed__0 = (const lean_object*)&l_Lake_help___closed__0_value;
static const lean_string_object l_Lake_help___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "init"};
static const lean_object* l_Lake_help___closed__1 = (const lean_object*)&l_Lake_help___closed__1_value;
static const lean_string_object l_Lake_help___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "build"};
static const lean_object* l_Lake_help___closed__2 = (const lean_object*)&l_Lake_help___closed__2_value;
static const lean_string_object l_Lake_help___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "check-build"};
static const lean_object* l_Lake_help___closed__3 = (const lean_object*)&l_Lake_help___closed__3_value;
static const lean_string_object l_Lake_help___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "query"};
static const lean_object* l_Lake_help___closed__4 = (const lean_object*)&l_Lake_help___closed__4_value;
static const lean_string_object l_Lake_help___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "update"};
static const lean_object* l_Lake_help___closed__5 = (const lean_object*)&l_Lake_help___closed__5_value;
static const lean_string_object l_Lake_help___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "upgrade"};
static const lean_object* l_Lake_help___closed__6 = (const lean_object*)&l_Lake_help___closed__6_value;
static const lean_string_object l_Lake_help___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "pack"};
static const lean_object* l_Lake_help___closed__7 = (const lean_object*)&l_Lake_help___closed__7_value;
static const lean_string_object l_Lake_help___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "unpack"};
static const lean_object* l_Lake_help___closed__8 = (const lean_object*)&l_Lake_help___closed__8_value;
static const lean_string_object l_Lake_help___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "upload"};
static const lean_object* l_Lake_help___closed__9 = (const lean_object*)&l_Lake_help___closed__9_value;
static const lean_string_object l_Lake_help___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "cache"};
static const lean_object* l_Lake_help___closed__10 = (const lean_object*)&l_Lake_help___closed__10_value;
static const lean_string_object l_Lake_help___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "test"};
static const lean_object* l_Lake_help___closed__11 = (const lean_object*)&l_Lake_help___closed__11_value;
static const lean_string_object l_Lake_help___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "check-test"};
static const lean_object* l_Lake_help___closed__12 = (const lean_object*)&l_Lake_help___closed__12_value;
static const lean_string_object l_Lake_help___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lint"};
static const lean_object* l_Lake_help___closed__13 = (const lean_object*)&l_Lake_help___closed__13_value;
static const lean_string_object l_Lake_help___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "check-lint"};
static const lean_object* l_Lake_help___closed__14 = (const lean_object*)&l_Lake_help___closed__14_value;
static const lean_string_object l_Lake_help___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "shake"};
static const lean_object* l_Lake_help___closed__15 = (const lean_object*)&l_Lake_help___closed__15_value;
static const lean_string_object l_Lake_help___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "script"};
static const lean_object* l_Lake_help___closed__16 = (const lean_object*)&l_Lake_help___closed__16_value;
static const lean_string_object l_Lake_help___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "scripts"};
static const lean_object* l_Lake_help___closed__17 = (const lean_object*)&l_Lake_help___closed__17_value;
static const lean_string_object l_Lake_help___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "serve"};
static const lean_object* l_Lake_help___closed__18 = (const lean_object*)&l_Lake_help___closed__18_value;
static const lean_string_object l_Lake_help___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "env"};
static const lean_object* l_Lake_help___closed__19 = (const lean_object*)&l_Lake_help___closed__19_value;
static const lean_string_object l_Lake_help___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "exe"};
static const lean_object* l_Lake_help___closed__20 = (const lean_object*)&l_Lake_help___closed__20_value;
static const lean_string_object l_Lake_help___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "exec"};
static const lean_object* l_Lake_help___closed__21 = (const lean_object*)&l_Lake_help___closed__21_value;
static const lean_string_object l_Lake_help___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lake_help___closed__22 = (const lean_object*)&l_Lake_help___closed__22_value;
static const lean_string_object l_Lake_help___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "translate-config"};
static const lean_object* l_Lake_help___closed__23 = (const lean_object*)&l_Lake_help___closed__23_value;
LEAN_EXPORT lean_object* l_Lake_help(lean_object*);
LEAN_EXPORT lean_object* l_Lake_help___boxed(lean_object*);
static lean_object* _init_l_Lake_usage___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_2_ = ((lean_object*)(l_Lake_usage___closed__0));
v___x_3_ = l_Lake_uiVersionString;
v___x_4_ = lean_string_append(v___x_3_, v___x_2_);
return v___x_4_;
}
}
static lean_object* _init_l_Lake_usage(void){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = lean_obj_once(&l_Lake_usage___closed__1, &l_Lake_usage___closed__1_once, _init_l_Lake_usage___closed__1);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Lake_helpScript(lean_object* v_x_77_){
_start:
{
lean_object* v___x_78_; uint8_t v___x_79_; 
v___x_78_ = ((lean_object*)(l_Lake_helpScript___closed__0));
v___x_79_ = lean_string_dec_eq(v_x_77_, v___x_78_);
if (v___x_79_ == 0)
{
lean_object* v___x_80_; uint8_t v___x_81_; 
v___x_80_ = ((lean_object*)(l_Lake_helpScript___closed__1));
v___x_81_ = lean_string_dec_eq(v_x_77_, v___x_80_);
if (v___x_81_ == 0)
{
lean_object* v___x_82_; uint8_t v___x_83_; 
v___x_82_ = ((lean_object*)(l_Lake_helpScript___closed__2));
v___x_83_ = lean_string_dec_eq(v_x_77_, v___x_82_);
if (v___x_83_ == 0)
{
lean_object* v___x_84_; 
v___x_84_ = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpScriptCli___closed__0));
return v___x_84_;
}
else
{
lean_object* v___x_85_; 
v___x_85_ = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpScriptDoc___closed__0));
return v___x_85_;
}
}
else
{
lean_object* v___x_86_; 
v___x_86_ = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpScriptRun___closed__0));
return v___x_86_;
}
}
else
{
lean_object* v___x_87_; 
v___x_87_ = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpScriptList___closed__0));
return v___x_87_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_helpScript___boxed(lean_object* v_x_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_Lake_helpScript(v_x_88_);
lean_dec_ref(v_x_88_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Lake_helpCache(lean_object* v_x_98_){
_start:
{
lean_object* v___x_99_; uint8_t v___x_100_; 
v___x_99_ = ((lean_object*)(l_Lake_helpCache___closed__0));
v___x_100_ = lean_string_dec_eq(v_x_98_, v___x_99_);
if (v___x_100_ == 0)
{
lean_object* v___x_101_; uint8_t v___x_102_; 
v___x_101_ = ((lean_object*)(l_Lake_helpCache___closed__1));
v___x_102_ = lean_string_dec_eq(v_x_98_, v___x_101_);
if (v___x_102_ == 0)
{
lean_object* v___x_103_; uint8_t v___x_104_; 
v___x_103_ = ((lean_object*)(l_Lake_helpCache___closed__2));
v___x_104_ = lean_string_dec_eq(v_x_98_, v___x_103_);
if (v___x_104_ == 0)
{
lean_object* v___x_105_; uint8_t v___x_106_; 
v___x_105_ = ((lean_object*)(l_Lake_helpCache___closed__3));
v___x_106_ = lean_string_dec_eq(v_x_98_, v___x_105_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; uint8_t v___x_108_; 
v___x_107_ = ((lean_object*)(l_Lake_helpCache___closed__4));
v___x_108_ = lean_string_dec_eq(v_x_98_, v___x_107_);
if (v___x_108_ == 0)
{
lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_109_ = ((lean_object*)(l_Lake_helpCache___closed__5));
v___x_110_ = lean_string_dec_eq(v_x_98_, v___x_109_);
if (v___x_110_ == 0)
{
lean_object* v___x_111_; uint8_t v___x_112_; 
v___x_111_ = ((lean_object*)(l_Lake_helpCache___closed__6));
v___x_112_ = lean_string_dec_eq(v_x_98_, v___x_111_);
if (v___x_112_ == 0)
{
lean_object* v___x_113_; uint8_t v___x_114_; 
v___x_113_ = ((lean_object*)(l_Lake_helpCache___closed__7));
v___x_114_ = lean_string_dec_eq(v_x_98_, v___x_113_);
if (v___x_114_ == 0)
{
lean_object* v___x_115_; 
v___x_115_ = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpCacheCli___closed__0));
return v___x_115_;
}
else
{
lean_object* v___x_116_; 
v___x_116_ = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpCacheServices___closed__0));
return v___x_116_;
}
}
else
{
lean_object* v___x_117_; 
v___x_117_ = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpCacheClean___closed__0));
return v___x_117_;
}
}
else
{
lean_object* v___x_118_; 
v___x_118_ = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpCachePutStaged___closed__0));
return v___x_118_;
}
}
else
{
lean_object* v___x_119_; 
v___x_119_ = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpCacheUnstage___closed__0));
return v___x_119_;
}
}
else
{
lean_object* v___x_120_; 
v___x_120_ = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpCacheStage___closed__0));
return v___x_120_;
}
}
else
{
lean_object* v___x_121_; 
v___x_121_ = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpCacheAdd___closed__0));
return v___x_121_;
}
}
else
{
lean_object* v___x_122_; 
v___x_122_ = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpCachePut___closed__0));
return v___x_122_;
}
}
else
{
lean_object* v___x_123_; 
v___x_123_ = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpCacheGet___closed__0));
return v___x_123_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_helpCache___boxed(lean_object* v_x_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Lake_helpCache(v_x_124_);
lean_dec_ref(v_x_124_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Lake_help(lean_object* v_x_150_){
_start:
{
lean_object* v___x_151_; uint8_t v___x_152_; 
v___x_151_ = ((lean_object*)(l_Lake_help___closed__0));
v___x_152_ = lean_string_dec_eq(v_x_150_, v___x_151_);
if (v___x_152_ == 0)
{
lean_object* v___x_153_; uint8_t v___x_154_; 
v___x_153_ = ((lean_object*)(l_Lake_help___closed__1));
v___x_154_ = lean_string_dec_eq(v_x_150_, v___x_153_);
if (v___x_154_ == 0)
{
lean_object* v___x_155_; uint8_t v___x_156_; 
v___x_155_ = ((lean_object*)(l_Lake_help___closed__2));
v___x_156_ = lean_string_dec_eq(v_x_150_, v___x_155_);
if (v___x_156_ == 0)
{
lean_object* v___x_157_; uint8_t v___x_158_; 
v___x_157_ = ((lean_object*)(l_Lake_help___closed__3));
v___x_158_ = lean_string_dec_eq(v_x_150_, v___x_157_);
if (v___x_158_ == 0)
{
lean_object* v___x_159_; uint8_t v___x_160_; 
v___x_159_ = ((lean_object*)(l_Lake_help___closed__4));
v___x_160_ = lean_string_dec_eq(v_x_150_, v___x_159_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; uint8_t v___x_162_; 
v___x_161_ = ((lean_object*)(l_Lake_help___closed__5));
v___x_162_ = lean_string_dec_eq(v_x_150_, v___x_161_);
if (v___x_162_ == 0)
{
lean_object* v___x_163_; uint8_t v___x_164_; 
v___x_163_ = ((lean_object*)(l_Lake_help___closed__6));
v___x_164_ = lean_string_dec_eq(v_x_150_, v___x_163_);
if (v___x_164_ == 0)
{
lean_object* v___x_165_; uint8_t v___x_166_; 
v___x_165_ = ((lean_object*)(l_Lake_help___closed__7));
v___x_166_ = lean_string_dec_eq(v_x_150_, v___x_165_);
if (v___x_166_ == 0)
{
lean_object* v___x_167_; uint8_t v___x_168_; 
v___x_167_ = ((lean_object*)(l_Lake_help___closed__8));
v___x_168_ = lean_string_dec_eq(v_x_150_, v___x_167_);
if (v___x_168_ == 0)
{
lean_object* v___x_169_; uint8_t v___x_170_; 
v___x_169_ = ((lean_object*)(l_Lake_help___closed__9));
v___x_170_ = lean_string_dec_eq(v_x_150_, v___x_169_);
if (v___x_170_ == 0)
{
lean_object* v___x_171_; uint8_t v___x_172_; 
v___x_171_ = ((lean_object*)(l_Lake_help___closed__10));
v___x_172_ = lean_string_dec_eq(v_x_150_, v___x_171_);
if (v___x_172_ == 0)
{
lean_object* v___x_173_; uint8_t v___x_174_; 
v___x_173_ = ((lean_object*)(l_Lake_help___closed__11));
v___x_174_ = lean_string_dec_eq(v_x_150_, v___x_173_);
if (v___x_174_ == 0)
{
lean_object* v___x_175_; uint8_t v___x_176_; 
v___x_175_ = ((lean_object*)(l_Lake_help___closed__12));
v___x_176_ = lean_string_dec_eq(v_x_150_, v___x_175_);
if (v___x_176_ == 0)
{
lean_object* v___x_177_; uint8_t v___x_178_; 
v___x_177_ = ((lean_object*)(l_Lake_help___closed__13));
v___x_178_ = lean_string_dec_eq(v_x_150_, v___x_177_);
if (v___x_178_ == 0)
{
lean_object* v___x_179_; uint8_t v___x_180_; 
v___x_179_ = ((lean_object*)(l_Lake_help___closed__14));
v___x_180_ = lean_string_dec_eq(v_x_150_, v___x_179_);
if (v___x_180_ == 0)
{
lean_object* v___x_181_; uint8_t v___x_182_; 
v___x_181_ = ((lean_object*)(l_Lake_helpCache___closed__6));
v___x_182_ = lean_string_dec_eq(v_x_150_, v___x_181_);
if (v___x_182_ == 0)
{
lean_object* v___x_183_; uint8_t v___x_184_; 
v___x_183_ = ((lean_object*)(l_Lake_help___closed__15));
v___x_184_ = lean_string_dec_eq(v_x_150_, v___x_183_);
if (v___x_184_ == 0)
{
lean_object* v___x_185_; uint8_t v___x_186_; 
v___x_185_ = ((lean_object*)(l_Lake_help___closed__16));
v___x_186_ = lean_string_dec_eq(v_x_150_, v___x_185_);
if (v___x_186_ == 0)
{
lean_object* v___x_187_; uint8_t v___x_188_; 
v___x_187_ = ((lean_object*)(l_Lake_help___closed__17));
v___x_188_ = lean_string_dec_eq(v_x_150_, v___x_187_);
if (v___x_188_ == 0)
{
lean_object* v___x_189_; uint8_t v___x_190_; 
v___x_189_ = ((lean_object*)(l_Lake_helpScript___closed__1));
v___x_190_ = lean_string_dec_eq(v_x_150_, v___x_189_);
if (v___x_190_ == 0)
{
lean_object* v___x_191_; uint8_t v___x_192_; 
v___x_191_ = ((lean_object*)(l_Lake_help___closed__18));
v___x_192_ = lean_string_dec_eq(v_x_150_, v___x_191_);
if (v___x_192_ == 0)
{
lean_object* v___x_193_; uint8_t v___x_194_; 
v___x_193_ = ((lean_object*)(l_Lake_help___closed__19));
v___x_194_ = lean_string_dec_eq(v_x_150_, v___x_193_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; uint8_t v___x_196_; 
v___x_195_ = ((lean_object*)(l_Lake_help___closed__20));
v___x_196_ = lean_string_dec_eq(v_x_150_, v___x_195_);
if (v___x_196_ == 0)
{
lean_object* v___x_197_; uint8_t v___x_198_; 
v___x_197_ = ((lean_object*)(l_Lake_help___closed__21));
v___x_198_ = lean_string_dec_eq(v_x_150_, v___x_197_);
if (v___x_198_ == 0)
{
lean_object* v___x_199_; uint8_t v___x_200_; 
v___x_199_ = ((lean_object*)(l_Lake_help___closed__22));
v___x_200_ = lean_string_dec_eq(v_x_150_, v___x_199_);
if (v___x_200_ == 0)
{
lean_object* v___x_201_; uint8_t v___x_202_; 
v___x_201_ = ((lean_object*)(l_Lake_help___closed__23));
v___x_202_ = lean_string_dec_eq(v_x_150_, v___x_201_);
if (v___x_202_ == 0)
{
lean_object* v___x_203_; 
v___x_203_ = l_Lake_usage;
return v___x_203_;
}
else
{
lean_object* v___x_204_; 
v___x_204_ = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpTranslateConfig___closed__0));
return v___x_204_;
}
}
else
{
lean_object* v___x_205_; 
v___x_205_ = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpLean___closed__0));
return v___x_205_;
}
}
else
{
lean_object* v___x_206_; 
v___x_206_ = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpExe___closed__0));
return v___x_206_;
}
}
else
{
lean_object* v___x_207_; 
v___x_207_ = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpExe___closed__0));
return v___x_207_;
}
}
else
{
lean_object* v___x_208_; 
v___x_208_ = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpEnv___closed__0));
return v___x_208_;
}
}
else
{
lean_object* v___x_209_; 
v___x_209_ = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpServe___closed__0));
return v___x_209_;
}
}
else
{
lean_object* v___x_210_; 
v___x_210_ = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpScriptRun___closed__0));
return v___x_210_;
}
}
else
{
lean_object* v___x_211_; 
v___x_211_ = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpScriptList___closed__0));
return v___x_211_;
}
}
else
{
lean_object* v___x_212_; 
v___x_212_ = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpScriptCli___closed__0));
return v___x_212_;
}
}
else
{
lean_object* v___x_213_; 
v___x_213_ = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpShake___closed__0));
return v___x_213_;
}
}
else
{
lean_object* v___x_214_; 
v___x_214_ = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpClean___closed__0));
return v___x_214_;
}
}
else
{
lean_object* v___x_215_; 
v___x_215_ = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpCheckLint___closed__0));
return v___x_215_;
}
}
else
{
lean_object* v___x_216_; 
v___x_216_ = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpLint___closed__0));
return v___x_216_;
}
}
else
{
lean_object* v___x_217_; 
v___x_217_ = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpCheckTest___closed__0));
return v___x_217_;
}
}
else
{
lean_object* v___x_218_; 
v___x_218_ = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpTest___closed__0));
return v___x_218_;
}
}
else
{
lean_object* v___x_219_; 
v___x_219_ = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpCacheCli___closed__0));
return v___x_219_;
}
}
else
{
lean_object* v___x_220_; 
v___x_220_ = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpUpload___closed__0));
return v___x_220_;
}
}
else
{
lean_object* v___x_221_; 
v___x_221_ = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpUnpack___closed__0));
return v___x_221_;
}
}
else
{
lean_object* v___x_222_; 
v___x_222_ = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpPack___closed__0));
return v___x_222_;
}
}
else
{
lean_object* v___x_223_; 
v___x_223_ = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpUpdate___closed__0));
return v___x_223_;
}
}
else
{
lean_object* v___x_224_; 
v___x_224_ = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpUpdate___closed__0));
return v___x_224_;
}
}
else
{
lean_object* v___x_225_; 
v___x_225_ = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpQuery___closed__0));
return v___x_225_;
}
}
else
{
lean_object* v___x_226_; 
v___x_226_ = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpCheckBuild___closed__0));
return v___x_226_;
}
}
else
{
lean_object* v___x_227_; 
v___x_227_ = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpBuild___closed__0));
return v___x_227_;
}
}
else
{
lean_object* v___x_228_; 
v___x_228_ = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpInit___closed__0));
return v___x_228_;
}
}
else
{
lean_object* v___x_229_; 
v___x_229_ = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpNew___closed__0));
return v___x_229_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_help___boxed(lean_object* v_x_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Lake_help(v_x_230_);
lean_dec_ref(v_x_230_);
return v_res_231_;
}
}
lean_object* runtime_initialize_Init_Data_ToString(uint8_t builtin);
lean_object* runtime_initialize_Lake_Version(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_CLI_Help(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_ToString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Version(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_usage = _init_l_Lake_usage();
lean_mark_persistent(l_Lake_usage);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_CLI_Help(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_ToString(uint8_t builtin);
lean_object* initialize_Lake_Version(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_CLI_Help(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ToString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Version(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_CLI_Help(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_CLI_Help(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_CLI_Help(builtin);
}
#ifdef __cplusplus
}
#endif
