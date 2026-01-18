/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
module

prelude
public import Init.Dynamic
public import Lake.Util.Version
public import Lake.Config.Pattern
public import Lake.Config.LeanConfig
public import Lake.Config.WorkspaceConfig
meta import all Lake.Config.Meta

open System Lean

namespace Lake

/-- The default `buildArchive` configuration for a package with `name`. -/
@[inline] public def defaultBuildArchive (name : Name) : String :=
  s!"{name.toString false}-{System.Platform.target}.tar.gz"

set_option linter.unusedVariables false in
/-- A `Package`'s declarative configuration. -/
public configuration PackageConfig (p : Name) (n : Name) extends WorkspaceConfig, LeanConfig where
  /-- **For internal use.** Whether this package is Lean itself. -/
  bootstrap : Bool := false

  /--
  **This field is deprecated.**

  The path of a package's manifest file, which stores the exact versions
  of its resolved dependencies.

  Defaults to `defaultManifestFile` (i.e., `lake-manifest.json`).
  -/
  manifestFile : Option FilePath := none

  /-- An `Array` of target names to build whenever the package is used. -/
  extraDepTargets : Array Name := #[]

  /--
  Whether to compile each of the package's module into a native shared library
  that is loaded whenever the module is imported. This speeds up evaluation of
  metaprograms and enables the interpreter to run functions marked `@[extern]`.

  Defaults to `false`.
  -/
  precompileModules : Bool := false

  /--
  Additional arguments to pass to the Lean language server
  (i.e., `lean --server`) launched by `lake serve`, both for this package and
  also for any packages browsed from this one in the same session.
  -/
  moreGlobalServerArgs, moreServerArgs : Array String := #[]

  /--
  The directory containing the package's Lean source files.
  Defaults to the package's directory.

  (This will be passed to `lean` as the `-R` option.)
  -/
  srcDir : FilePath := "."

  /--
  The directory to which Lake should output the package's build results.
  Defaults to `defaultBuildDir` (i.e., `.lake/build`).
  -/
  buildDir : FilePath := defaultBuildDir

  /--
  The build subdirectory to which Lake should output the package's
  binary Lean libraries (e.g., `.olean`, `.ilean` files).
  Defaults to  `defaultLeanLibDir` (i.e., `lib`).
  -/
  leanLibDir : FilePath := defaultLeanLibDir

  /--
  The build subdirectory to which Lake should output the package's
  native libraries (e.g., `.a`, `.so`, `.dll` files).
  Defaults to `defaultNativeLibDir` (i.e., `lib`).
  -/
  nativeLibDir : FilePath := defaultNativeLibDir

  /--
  The build subdirectory to which Lake should output the package's binary executable.
  Defaults to `defaultBinDir` (i.e., `bin`).
  -/
  binDir : FilePath := defaultBinDir

  /--
  The build subdirectory to which Lake should output
  the package's intermediary results (e.g., `.c` and `.o` files).
  Defaults to `defaultIrDir` (i.e., `ir`).
  -/
  irDir : FilePath := defaultIrDir

  /--
  The URL of the GitHub repository to upload and download releases of this package.
  If `none` (the default), for downloads, Lake uses the URL the package was download
  from (if it is a dependency) and for uploads, uses `gh`'s default.
  -/
  releaseRepo, releaseRepo? : Option String := none

  /--
  A custom name for the build archive for the GitHub cloud release.
  If `none` (the default), Lake defaults to `{(pkg-)name}-{System.Platform.target}.tar.gz`.
  -/
  buildArchive, buildArchive? : Option String := none

  /--
  Whether to prefer downloading a prebuilt release (from GitHub) rather than
  building this package from the source when this package is used as a dependency.
  -/
  preferReleaseBuild : Bool := false

  /--
  The name of the script, executable, or library by `lake test` when
  this package is the workspace root. To point to a definition in another
  package, use the syntax `<pkg>/<def>`.

  A script driver will be run by `lake test` with the arguments
  configured in `testDriverArgs`  followed by any specified on the CLI
  (e.g., via  `lake lint -- <args>...`). An executable driver will be built
  and then run like a script. A library will just be built.
  -/
  testDriver, testRunner : String := ""

  /--
  Arguments to pass to the package's test driver.
  These arguments will come before those passed on the command line via
  `lake test -- <args>...`.
  -/
  testDriverArgs : Array String := #[]

  /--
  The name of the script or executable used by `lake lint` when this package
  is the workspace root. To point to a definition in another package, use the
  syntax `<pkg>/<def>`.

  A script driver will be run by `lake lint` with the arguments
  configured in `lintDriverArgs` followed by any specified on the CLI
  (e.g., via  `lake lint -- <args>...`). An executable driver will be built
  and then run like a script.
  -/
  lintDriver : String := ""

  /--
  Arguments to pass to the package's linter.
  These arguments will come before those passed on the command line via
  `lake lint -- <args>...`.
  -/
  lintDriverArgs : Array String := #[]

  /--
  The package version. Versions have the form:

  ```
  v!"<major>.<minor>.<patch>[-<specialDescr>]"
  ```

  A version with a `-` suffix is considered a "prerelease".

  Lake suggest the following guidelines for incrementing versions:

  * **Major version increment** *(e.g., v1.3.0 → v2.0.0)*
    Indicates significant breaking changes in the package.
    Package users are not expected to update to the new version
    without manual intervention.

  * **Minor version increment** *(e.g., v1.3.0 → v1.4.0)*
    Denotes notable changes that are expected to be
    generally backwards compatible.
    Package users are expected to update to this version automatically
    and should be able to fix any breakages and/or warnings easily.

  * **Patch version increment** *(e.g., v1.3.0 → v1.3.1)*
    Reserved for bug fixes and small touchups.
    Package users are expected to update automatically and should not expect
    significant breakage, except in the edge case of users relying on the
    behavior of patched bugs.

  **Note that backwards-incompatible changes may occur at any version increment.**
  The is because the current nature of Lean (e.g., transitive imports,
  rich metaprogramming, reducibility in proofs), makes it infeasible to
  define a completely stable interface for a package.
  Instead, the different version levels indicate a change's intended significance
  and how difficult migration is expected to be.

  Versions of form the `0.x.x` are considered development versions prior to
  first official release. Like prerelease, they are not expected to closely
  follow the above guidelines.

  Packages without a defined version default to `0.0.0`.
  -/
  version : StdVer := {}

  /--
  Git tags of this package's repository that should be treated as versions.
  Package indices (e.g., Reservoir) can make use of this information to determine
  the Git revisions corresponding to released versions.

  Defaults to tags that are "version-like".
  That is, start with a `v` followed by a digit.
  -/
  versionTags : StrPat := defaultVersionTags

  /-- A short description for the package (e.g., for Reservoir). -/
  description : String := ""

  /--
  Custom keywords associated with the package.
  Reservoir can make use of a package's keywords to group related packages
  together and make it easier for users to discover them.

  Good keywords include the domain (e.g., `math`, `software-verification`,
  `devtool`), specific subtopics (e.g., `topology`,  `cryptology`), and
  significant implementation details (e.g., `dsl`, `ffi`, `cli`).
  For instance, Lake's keywords could be `devtool`, `cli`, `dsl`,
  `package-manager`, and `build-system`.
  -/
  keywords : Array String := #[]

  /--
  A URL to information about the package.

  Reservoir will already include a link to the package's GitHub repository
  (if the package is sourced from there). Thus, users are advised to specify
  something else for this (if anything).
  -/
  homepage : String := ""

  /--
  The package's license (if one).
  Should be a valid [SPDX License Expression][1].

  Reservoir requires that packages uses an OSI-approved license to be
  included in its index, and currently only supports single identifier
  SPDX expressions. For, a list of OSI-approved SPDX license identifiers,
  see the [SPDX LIcense List][2].

  [1]: https://spdx.github.io/spdx-spec/v3.0/annexes/SPDX-license-expressions/
  [2]: https://spdx.org/licenses/
  -/
  license : String := ""

  /--
  Files containing licensing information for the package.

  These should be the license files that users are expected to include when
  distributing package sources, which may be more then one file for some licenses.
  For example, the Apache 2.0 license requires the reproduction of a `NOTICE`
  file along with the license (if such a file exists).

  Defaults to `#["LICENSE"]`.
  -/
  licenseFiles : Array FilePath := #["LICENSE"]

  /--
  The path to the package's README.

  A README should be a Markdown file containing an overview of the package.
  Reservoir displays the rendered HTML of this file on a package's page.
  A nonstandard location can be used to provide a different README for Reservoir
  and GitHub.

  Defaults to `README.md`.
  -/
  readmeFile : FilePath := "README.md"

  /--
  Whether Reservoir should include the package in its index.
  When set to `false`, Reservoir will not add the package to its index
  and will remove it if it was already there (when Reservoir is next updated).
  -/
  reservoir : Bool := true

  /--
  Whether to enables Lake's local, offline artifact cache for the package.

  Artifacts (i.e., build products) of packages will be shared across
  local copies by storing them in a cache associated with the Lean toolchain.
  This can significantly reduce initial build times and disk space usage when
  working with multiple copies of large projects or large dependencies.

  As a caveat, build targets which support the artifact cache will not be stored
  in their usual location within the build directory. Thus, projects with custom build
  scripts that rely on specific location of artifacts may wish to disable this feature.

  If `none` (the default), this will fallback to (in order):
  * The `LAKE_ARTIFACT_CACHE` environment variable (if set)
  * The workspace root's `enableArtifactCache` configuration (if set and this package is a dependency)
  * Lake's default: `false`
  -/
  enableArtifactCache?, enableArtifactCache : Option Bool := none

  /--
  Whether, when the local artifact cache is enabled, Lake should copy all cached
  artifacts into the build directory. This ensures the build results are available
  to external consumers who expect them in the build directory.

  Defaults to `false`.
  -/
  restoreAllArtifacts : Bool := false

  /--
  Whether native libraries (of this package) should be prefixed with `lib` on Windows.

  Unlike Unix, Windows does not require native libraries to start with `lib` and,
  by convention, they usually do not. However, for consistent naming across all platforms,
  users may wish to enable this.

  Defaults to `false`.
  -/
  libPrefixOnWindows : Bool := false

  /--
  Whether downstream packages can `import all` modules of this package.

  If enabled, downstream users will be able to access the `private` internals of modules,
  including definition bodies not marked as `@[expose]`.
  This may also, in the future, prevent compiler optimization which rely on `private`
  definitions being inaccessible outside their own package.

  Defaults to `false`.
  -/
  allowImportAll : Bool := false

deriving Inhabited

/-- The package's name as specified by the author. -/
public abbrev PackageConfig.origName (_ : PackageConfig p n) := n

/-- A package declaration from a configuration written in Lean. -/
public structure PackageDecl where
  name : Name
  origName : Name
  config : PackageConfig name origName
  deriving TypeName
