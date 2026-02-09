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
static const lean_string_object l_Lake_usage___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3535, .m_capacity = 3535, .m_length = 3534, .m_data = "\n\nUSAGE:\n  lake [OPTIONS] <COMMAND>\n\nCOMMANDS:\n  new <name> <temp>     create a Lean package in a new directory\n  init <name> <temp>    create a Lean package in the current directory\n  build <targets>...    build targets\n  query <targets>...    build targets and output results\n  exe <exe> <args>...   build an exe and run it in Lake's environment\n  check-build           check if any default build targets are configured\n  test                  test the package using the configured test driver\n  check-test            check if there is a properly configured test driver\n  lint                  lint the package using the configured lint driver\n  check-lint            check if there is a properly configured lint driver\n  clean                 remove build outputs\n  shake                 minimize imports in source files\n  env <cmd> <args>...   execute a command in Lake's environment\n  lean <file>           elaborate a Lean file in Lake's context\n  update                update dependencies and save them to the manifest\n  pack                  pack build artifacts into an archive for distribution\n  unpack                unpack build artifacts from an distributed archive\n  upload <tag>          upload build artifacts to a GitHub release\n  cache                 manage the Lake cache\n  script                manage and run workspace scripts\n  scripts               shorthand for `lake script list`\n  run <script>          shorthand for `lake script run`\n  translate-config      change language of the package configuration\n  serve                 start the Lean language server\n\nBASIC OPTIONS:\n  --version             print version and exit\n  --help, -h            print help of the program or a command and exit\n  --dir, -d=file        use the package configuration in a specific directory\n  --file, -f=file       use a specific file for the package configuration\n  -K key[=value]        set the configuration file option named key\n  --old                 only rebuild modified modules (ignore transitive deps)\n  --rehash, -H          hash all files for traces (do not trust `.hash` files)\n  --update              update dependencies on load (e.g., before a build)\n  --packages=file       JSON file of package entries that override the manifest\n  --reconfigure, -R     elaborate configuration files instead of using OLeans\n  --keep-toolchain      do not update toolchain on workspace update\n  --no-build            exit immediately if a build target is not up-to-date\n  --no-cache            build packages locally; do not download build caches\n  --try-cache           attempt to download build caches for supported packages\n  --json, -J            output JSON-formatted results (in `lake query`)\n  --text                output results as plain text (in `lake query`)\n\nOUTPUT OPTIONS:\n  --quiet, -q           hide informational logs and the progress indicator\n  --verbose, -v         show trace logs (command invocations) and built targets\n  --ansi, --no-ansi     toggle the use of ANSI escape codes to prettify output\n  --log-level=lv        minimum log level to output on success\n                        (levels: trace, info, warning, error)\n  --fail-level=lv       minimum log level to fail a build (default: error)\n  --iofail              fail build if any I/O or other info is logged\n                        (same as --fail-level=info)\n  --wfail               fail build if warnings are logged\n                        (same as --fail-level=warning)\n\n\nSee `lake help <command>` for more information on a specific command."};
static const lean_object* l_Lake_usage___closed__0 = (const lean_object*)&l_Lake_usage___closed__0_value;
extern lean_object* l_Lake_uiVersionString;
lean_object* lean_string_append(lean_object*, lean_object*);
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
static const lean_string_object l___private_Lake_CLI_Help_0__Lake_helpLint___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 560, .m_capacity = 560, .m_length = 559, .m_data = "Lint the workspace's root package using its configured lint driver\n\nUSAGE:\n  lake lint [-- <args>...]\n\nA lint driver can be configured by either setting the `lintDriver` package\nconfiguration option by tagging a script or executable `@[lint_driver]`.\nA definition in dependency can be used as a test driver by using the\n`<pkg>/<name>` syntax for the 'testDriver' configuration option.\n\nA script lint driver will be run with the  package configuration's\n`lintDriverArgs` plus the CLI `args`. An executable lint driver will be\nbuilt and then run like a script.\n"};
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
static const lean_string_object l___private_Lake_CLI_Help_0__Lake_helpCacheCli___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 263, .m_capacity = 263, .m_length = 262, .m_data = "Manage the Lake cache\n\nUSAGE:\n  lake cache <COMMAND>\n\nCOMMANDS:\n  get [<mappings>]      download artifacts into the Lake cache\n  put <mappings>        upload artifacts to a remote cache\n\nSee `lake cache help <command>` for more information on a specific command."};
static const lean_object* l___private_Lake_CLI_Help_0__Lake_helpCacheCli___closed__0 = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpCacheCli___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Help_0__Lake_helpCacheCli = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpCacheCli___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Help_0__Lake_helpCacheGet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2518, .m_capacity = 2518, .m_length = 2517, .m_data = "Download artifacts from a remote service into the Lake cache\n\nUSAGE:\n  lake cache get [<mappings>]\n\nOPTIONS:\n  --max-revs=<n>                  backtrack up to n revisions (default: 100)\n  --rev=<commit-hash>             uses this exact revision to lookup artifacts\n  --repo=<github-repo>            GitHub repository of the package or a fork\n  --platform=<target-triple>      with Reservoir or --repo, sets the platform\n  --toolchain=<name>              with Reservoir or --repo, sets the toolchain\n  --scope=<remote-scope>          scope for a custom endpoint\n\nDownloads artifacts for packages in the workspace from a remote cache service.\nThe cache service used can be configured via the environment variables:\n\n  LAKE_CACHE_ARTIFACT_ENDPOINT  base URL for artifact downloads\n  LAKE_CACHE_REVISION_ENDPOINT  base URL for the mapping download\n\nIf neither of these are set, Lake will use Reservoir.\n\nIf an input-to-outputs mappings file, `--scope`, or `--repo` is provided,\nLake will download artifacts for the root package. Otherwise, it will use\nReservoir to download artifacts for each dependency in workspace (in order).\nNon-Reservoir dependencies will be skipped.\n\nTo determine the artifacts to download, Lake searches for input-to-output\nmappings for a given build of the package via the cache service. This mapping\nis identified by a Git revision and prefixed with a scope derived from the\npackage's name, GitHub repository, Lean toolchain, and current platform.\nThe exact configuration can be customized using options.\n\nFor Reservoir, setting `--repo` will make Lake lookup artifacts for the root\npackage by a repository name, rather than the package's. This can be used to\ndownload artifacts for a fork of the Reservoir package (if such artifacts are\navailable). The `--platform` and `--toolchain` options can be used to download\nartifacts for a different platform/toolchain configuration than Lake detects.\nFor a custom endpoint, the full prefix Lake uses can be set via  `--scope`.\n\nIf `--rev` is not set, Lake uses the package's current revision to lookup\nartifacts. If no mappings are found, Lake will backtrack the Git history up to\n`--max-revs`, looking for a revision with mappings. If `--max-revs` is 0, Lake\nwill search the repository's entire history (or as far as Git will allow).\n\nIf a download for an artifact fails or the download process for a whole\npackage fails, Lake will report this and continue on to the next. Once done,\nif any download failed, Lake will exit with a nonzero status code."};
static const lean_object* l___private_Lake_CLI_Help_0__Lake_helpCacheGet___closed__0 = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpCacheGet___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Help_0__Lake_helpCacheGet = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpCacheGet___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Help_0__Lake_helpCachePut___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1764, .m_capacity = 1764, .m_length = 1763, .m_data = "Upload artifacts from the Lake cache to a remote service\n\nUSAGE:\n  lake cache put <mappings> <scope-option>\n\nUploads the input-to-outputs mappings contained in the specified file along\nwith the corresponding output artifacts to a remote cache. The cache service\nused is configured via the environment variables:\n\n  LAKE_CACHE_KEY                  authentication key for requests\n  LAKE_CACHE_ARTIFACT_ENDPOINT    base URL for artifact uploads\n  LAKE_CACHE_REVISION_ENDPOINT    base URL for the mapping upload\n\nFiles are uploaded using the AWS Signature Version 4 authentication protocol\nvia `curl`. Thus, the service should generally be an S3-compatible bucket.\n\nSince Lake does not currently use cryptographically secure hashes for\nartifacts and outputs, uploads to the cache are prefixed with a scope to avoid\nclashes. This scoped is configured with the following options:\n\n  --scope=<remote-scope>          sets a fixed scope\n  --repo=<github-repo>            uses the repository + toolchain & platform\n  --toolchain=<name>              with --repo, sets the toolchain\n  --platform=<target-triple>      with --repo, sets the platform\n\nAt least one of `--scope` or `--repo` must be set. If `--repo` is used, Lake\nwill produce a scope by augmenting the repository with toolchain and platform\ninformation as it deems necessary. If `--scope` is set, Lake will use the\nspecified scope verbatim.\n\nArtifacts are uploaded to the artifact endpoint with a file name derived\nfrom their Lake content hash (and prefixed by the repository or scope).\nThe mappings file is uploaded to the revision endpoint with a file name\nderived from the package's current Git revision (and prefixed by the\nfull scope). As such, the command will warn if the work tree currently\nhas changes."};
static const lean_object* l___private_Lake_CLI_Help_0__Lake_helpCachePut___closed__0 = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpCachePut___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Help_0__Lake_helpCachePut = (const lean_object*)&l___private_Lake_CLI_Help_0__Lake_helpCachePut___closed__0_value;
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
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_helpScript(lean_object*);
LEAN_EXPORT lean_object* l_Lake_helpScript___boxed(lean_object*);
static const lean_string_object l_Lake_helpCache___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "get"};
static const lean_object* l_Lake_helpCache___closed__0 = (const lean_object*)&l_Lake_helpCache___closed__0_value;
static const lean_string_object l_Lake_helpCache___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "put"};
static const lean_object* l_Lake_helpCache___closed__1 = (const lean_object*)&l_Lake_helpCache___closed__1_value;
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
static const lean_string_object l_Lake_help___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "clean"};
static const lean_object* l_Lake_help___closed__15 = (const lean_object*)&l_Lake_help___closed__15_value;
static const lean_string_object l_Lake_help___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "shake"};
static const lean_object* l_Lake_help___closed__16 = (const lean_object*)&l_Lake_help___closed__16_value;
static const lean_string_object l_Lake_help___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "script"};
static const lean_object* l_Lake_help___closed__17 = (const lean_object*)&l_Lake_help___closed__17_value;
static const lean_string_object l_Lake_help___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "scripts"};
static const lean_object* l_Lake_help___closed__18 = (const lean_object*)&l_Lake_help___closed__18_value;
static const lean_string_object l_Lake_help___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "serve"};
static const lean_object* l_Lake_help___closed__19 = (const lean_object*)&l_Lake_help___closed__19_value;
static const lean_string_object l_Lake_help___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "env"};
static const lean_object* l_Lake_help___closed__20 = (const lean_object*)&l_Lake_help___closed__20_value;
static const lean_string_object l_Lake_help___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "exe"};
static const lean_object* l_Lake_help___closed__21 = (const lean_object*)&l_Lake_help___closed__21_value;
static const lean_string_object l_Lake_help___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "exec"};
static const lean_object* l_Lake_help___closed__22 = (const lean_object*)&l_Lake_help___closed__22_value;
static const lean_string_object l_Lake_help___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lake_help___closed__23 = (const lean_object*)&l_Lake_help___closed__23_value;
static const lean_string_object l_Lake_help___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "translate-config"};
static const lean_object* l_Lake_help___closed__24 = (const lean_object*)&l_Lake_help___closed__24_value;
LEAN_EXPORT lean_object* l_Lake_help(lean_object*);
LEAN_EXPORT lean_object* l_Lake_help___boxed(lean_object*);
static lean_object* _init_l_Lake_usage___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lake_usage___closed__0));
x_2 = l_Lake_uiVersionString;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_usage() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_usage___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_helpScript(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = ((lean_object*)(l_Lake_helpScript___closed__0));
x_3 = lean_string_dec_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_Lake_helpScript___closed__1));
x_5 = lean_string_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = ((lean_object*)(l_Lake_helpScript___closed__2));
x_7 = lean_string_dec_eq(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpScriptCli___closed__0));
return x_8;
}
else
{
lean_object* x_9; 
x_9 = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpScriptDoc___closed__0));
return x_9;
}
}
else
{
lean_object* x_10; 
x_10 = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpScriptRun___closed__0));
return x_10;
}
}
else
{
lean_object* x_11; 
x_11 = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpScriptList___closed__0));
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lake_helpScript___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_helpScript(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_helpCache(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = ((lean_object*)(l_Lake_helpCache___closed__0));
x_3 = lean_string_dec_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_Lake_helpCache___closed__1));
x_5 = lean_string_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpCacheCli___closed__0));
return x_6;
}
else
{
lean_object* x_7; 
x_7 = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpCachePut___closed__0));
return x_7;
}
}
else
{
lean_object* x_8; 
x_8 = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpCacheGet___closed__0));
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lake_helpCache___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_helpCache(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_help(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = ((lean_object*)(l_Lake_help___closed__0));
x_3 = lean_string_dec_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_Lake_help___closed__1));
x_5 = lean_string_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = ((lean_object*)(l_Lake_help___closed__2));
x_7 = lean_string_dec_eq(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = ((lean_object*)(l_Lake_help___closed__3));
x_9 = lean_string_dec_eq(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = ((lean_object*)(l_Lake_help___closed__4));
x_11 = lean_string_dec_eq(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = ((lean_object*)(l_Lake_help___closed__5));
x_13 = lean_string_dec_eq(x_1, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = ((lean_object*)(l_Lake_help___closed__6));
x_15 = lean_string_dec_eq(x_1, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = ((lean_object*)(l_Lake_help___closed__7));
x_17 = lean_string_dec_eq(x_1, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = ((lean_object*)(l_Lake_help___closed__8));
x_19 = lean_string_dec_eq(x_1, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = ((lean_object*)(l_Lake_help___closed__9));
x_21 = lean_string_dec_eq(x_1, x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = ((lean_object*)(l_Lake_help___closed__10));
x_23 = lean_string_dec_eq(x_1, x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = ((lean_object*)(l_Lake_help___closed__11));
x_25 = lean_string_dec_eq(x_1, x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = ((lean_object*)(l_Lake_help___closed__12));
x_27 = lean_string_dec_eq(x_1, x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = ((lean_object*)(l_Lake_help___closed__13));
x_29 = lean_string_dec_eq(x_1, x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = ((lean_object*)(l_Lake_help___closed__14));
x_31 = lean_string_dec_eq(x_1, x_30);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = ((lean_object*)(l_Lake_help___closed__15));
x_33 = lean_string_dec_eq(x_1, x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = ((lean_object*)(l_Lake_help___closed__16));
x_35 = lean_string_dec_eq(x_1, x_34);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = ((lean_object*)(l_Lake_help___closed__17));
x_37 = lean_string_dec_eq(x_1, x_36);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = ((lean_object*)(l_Lake_help___closed__18));
x_39 = lean_string_dec_eq(x_1, x_38);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = ((lean_object*)(l_Lake_helpScript___closed__1));
x_41 = lean_string_dec_eq(x_1, x_40);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = ((lean_object*)(l_Lake_help___closed__19));
x_43 = lean_string_dec_eq(x_1, x_42);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = ((lean_object*)(l_Lake_help___closed__20));
x_45 = lean_string_dec_eq(x_1, x_44);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = ((lean_object*)(l_Lake_help___closed__21));
x_47 = lean_string_dec_eq(x_1, x_46);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = ((lean_object*)(l_Lake_help___closed__22));
x_49 = lean_string_dec_eq(x_1, x_48);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = ((lean_object*)(l_Lake_help___closed__23));
x_51 = lean_string_dec_eq(x_1, x_50);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = ((lean_object*)(l_Lake_help___closed__24));
x_53 = lean_string_dec_eq(x_1, x_52);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = l_Lake_usage;
return x_54;
}
else
{
lean_object* x_55; 
x_55 = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpTranslateConfig___closed__0));
return x_55;
}
}
else
{
lean_object* x_56; 
x_56 = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpLean___closed__0));
return x_56;
}
}
else
{
lean_object* x_57; 
x_57 = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpExe___closed__0));
return x_57;
}
}
else
{
lean_object* x_58; 
x_58 = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpExe___closed__0));
return x_58;
}
}
else
{
lean_object* x_59; 
x_59 = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpEnv___closed__0));
return x_59;
}
}
else
{
lean_object* x_60; 
x_60 = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpServe___closed__0));
return x_60;
}
}
else
{
lean_object* x_61; 
x_61 = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpScriptRun___closed__0));
return x_61;
}
}
else
{
lean_object* x_62; 
x_62 = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpScriptList___closed__0));
return x_62;
}
}
else
{
lean_object* x_63; 
x_63 = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpScriptCli___closed__0));
return x_63;
}
}
else
{
lean_object* x_64; 
x_64 = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpShake___closed__0));
return x_64;
}
}
else
{
lean_object* x_65; 
x_65 = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpClean___closed__0));
return x_65;
}
}
else
{
lean_object* x_66; 
x_66 = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpCheckLint___closed__0));
return x_66;
}
}
else
{
lean_object* x_67; 
x_67 = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpLint___closed__0));
return x_67;
}
}
else
{
lean_object* x_68; 
x_68 = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpCheckTest___closed__0));
return x_68;
}
}
else
{
lean_object* x_69; 
x_69 = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpTest___closed__0));
return x_69;
}
}
else
{
lean_object* x_70; 
x_70 = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpCacheCli___closed__0));
return x_70;
}
}
else
{
lean_object* x_71; 
x_71 = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpUpload___closed__0));
return x_71;
}
}
else
{
lean_object* x_72; 
x_72 = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpUnpack___closed__0));
return x_72;
}
}
else
{
lean_object* x_73; 
x_73 = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpPack___closed__0));
return x_73;
}
}
else
{
lean_object* x_74; 
x_74 = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpUpdate___closed__0));
return x_74;
}
}
else
{
lean_object* x_75; 
x_75 = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpUpdate___closed__0));
return x_75;
}
}
else
{
lean_object* x_76; 
x_76 = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpQuery___closed__0));
return x_76;
}
}
else
{
lean_object* x_77; 
x_77 = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpCheckBuild___closed__0));
return x_77;
}
}
else
{
lean_object* x_78; 
x_78 = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpBuild___closed__0));
return x_78;
}
}
else
{
lean_object* x_79; 
x_79 = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpInit___closed__0));
return x_79;
}
}
else
{
lean_object* x_80; 
x_80 = ((lean_object*)(l___private_Lake_CLI_Help_0__Lake_helpNew___closed__0));
return x_80;
}
}
}
LEAN_EXPORT lean_object* l_Lake_help___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_help(x_1);
lean_dec_ref(x_1);
return x_2;
}
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
l_Lake_usage___closed__1 = _init_l_Lake_usage___closed__1();
lean_mark_persistent(l_Lake_usage___closed__1);
l_Lake_usage = _init_l_Lake_usage();
lean_mark_persistent(l_Lake_usage);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
