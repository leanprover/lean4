# Lake

Lake (Lean Make) is the new build system and package manager for Lean 4.
With Lake, the package's configuration is written in Lean inside a dedicated `lakefile.lean` stored in the root of the package's directory.

Each `lakefile.lean` includes a `package` declaration (akin to `main`) which defines the package's basic configuration. It also typically includes build configurations for different targets (e.g., Lean libraries and binary executables) and Lean scripts to run on the command line (via `lake script run`).

***This README provides information about Lake relative to the current commit. If you are looking for documentation for the Lake version shipped with a given Lean release, you should look at the README of that version.***

## Table of Contents

* [Getting Lake](#getting-lake)
* [Creating and Building a Package](#creating-and-building-a-package)
* [Glossary of Terms](#glossary-of-terms)
* [Package Configuration Options](#package-configuration-options)
  + [Layout](#layout)
  + [Build & Run](#build--run)
  + [Cloud Releases](#cloud-releases)
* [Defining Build Targets](#defining-build-targets)
  + [Lean Libraries](#lean-libraries)
  + [Binary Executables](#binary-executables)
  + [External Libraries](#external-libraries)
  + [Custom Targets](#custom-targets)
* [Defining New Facets](#defining-new-facets)
* [Adding Dependencies](#adding-dependencies)
  + [Syntax of `require`](#syntax-of-require)
* [GitHub Release Builds](#github-release-builds)
* [Writing and Running Scripts](#writing-and-running-scripts)
* [Building and Running Lake from the Source](#building-and-running-lake-from-the-source)
  + [Building with Nix Flakes](#building-with-nix-flakes)
  + [Augmenting Lake's Search Path](#augmenting-lakes-search-path)

## Getting Lake

Lake is part of the [lean4](https://github.com/leanprover/lean4) repository and is distributed along with its official releases (e.g., as part of the [elan](https://github.com/leanprover/elan) toolchain). So if you have installed a semi-recent Lean 4 nightly, you should already have it! If you want to build the latest version from the source yourself, check out the [build instructions](#building-and-running-lake-from-the-source) at the bottom of this README.

## Creating and Building a Package

To create a new package, either run `lake init <package-name> [<template>]` to setup the package in the current directory or `lake new <package-name> [<template>]` to create it in a new directory. For example, we could create the package `hello` like so:

```
$ mkdir hello
$ cd hello
$ lake init hello
```

or like so:

```
$ lake new hello
$ cd hello
```

Either way, Lake will create the following template directory structure and initialize a Git repository for the package.

```
.lake/         # Lake output directory
Hello/         # library source files; accessible via `import Hello.*`
  Basic.lean   # an example library module file
  ...          # additional files should be added here
Hello.lean     # library root; imports standard modules from Hello
Main.lean      # main file of the executable (contains `def main`)
lakefile.lean  # Lake package configuration
lean-toolchain # the Lean version used by the package
.gitignore     # excludes system-specific files (e.g. `build`) from Git
```

The example modules files contain the following dummy "Hello World" program.

**Hello/Basic.lean**
```lean
def hello := "world"
```

**Hello.lean**
```lean
-- This module serves as the root of the `Hello` library.
-- Import modules here that should be built as part of the library.
import «Hello».Basic
```

**Main.lean**
```lean
import «Hello»

def main : IO Unit :=
  IO.println s!"Hello, {hello}!"
```

Lake also creates a basic `lakefile.lean` for the package along with a `lean-toolchain` file that contains the name of the Lean toolchain Lake belongs to, which tells [`elan`](https://github.com/leanprover/elan) to use that Lean toolchain for the package.


**lakefile.lean**
```lean
import Lake
open Lake DSL

package «hello» where
  -- add package configuration options here

lean_lib «Hello» where
  -- add library configuration options here

@[default_target]
lean_exe «hello» where
  root := `Main
```

The command `lake build` is used to build the package (and its [dependencies](#adding-dependencies), if it has them) into a native executable. The result will be placed in `.lake/build/bin`. The command `lake clean` deletes `build`.

```
$ lake build
...
$ ./.lake/build/bin/hello
Hello, world!
```

Examples of different package configurations can be found in the [`examples`](examples) folder of this repository. You can also specified a particular configuration file template when using `lake init` or `lake new` to control what files Lake creates. See `lake help init` or `lake help new` for details.

## Glossary of Terms

Lake uses a lot of terms common in software development -- like workspace, package, library, executable, target, etc. -- and some more esoteric ones -- like facet. However, whether common or not, these terms mean different things to different people, so it is important to elucidate how Lake defines these terms:

* A **package** is the **fundamental unit of code distribution in Lake**.  Packages can be sourced from the local file system or downloaded from the web (e.g., via Git). The `package` declaration in package's lakefile names it and [defines its basic properties](#package-configuration-options).

* A **lakefile** is the Lean file that configures a package. It defines how to view, edit, build, and run the code within it, and it specifies what other packages it may require in order to do so.

* If package `B` requires package `A`, then package `A` is a **dependency** of package B and package `B` is its **dependent**. Package `A` is **upstream** of package `B` and package `B` is reversely **downstream** of package `A`. See the [Adding Dependencies section](#adding-dependencies) for details on how to specify dependencies.

* A **workspace** is the **broadest organizational unit in Lake**. It bundles together a package (termed the **root**), its transitive dependencies, and Lake's environment. Every package can operate as the root of a workspace and the workspace will derive its configuration from this root.

* A **module** is the **smallest unit of code visible to Lake's build system**. It is generally represented by a Lean source file and a set of binary libraries (i.e., a Lean `olean` and `ilean` plus a system shared library if `precompileModules` is turned on). Modules can import one another in order to use each other's code and Lake exists primarily to facilitate this process.

* A **Lean library** is a collection of modules that share a single configuration. Its configuration defines a set of **module roots** that determines which modules are part of the library, and a set of **module globs** that selects which modules to build on a `lake build` of the library.  See the [Lean Libraries section](#lean-libraries) for more details.

* A **Lean binary executable** is a binary executable (i.e., a program a user can run on their computer without Lean installed) built from a Lean module termed its **root** (which should have a `main` definition). See the [Binary Executables section](#binary-executables) for more details.

* An **external library** is a native (static) library built from foreign code (e.g., C) that is required by a package's Lean code in order to function (e.g., because it uses `@[extern]` to invoke code written in a foreign language). An `extern_lib` target is used to inform Lake of such a requirement and instruct Lake on how to build requisite library. Lake then automatically links the external library when appropriate to give the Lean code access to the foreign functions (or, more technically, the foreign symbols) it needs. See the [External Libraries section](#external-libraries) for more details.

* A **target** is the **fundamental build unit of Lake**. A package can defining any number of targets. Each target has a name, which is used to instruct Lake to build the target (e.g., through `lake build <target>`) and to keep track internally of a target's build status.  Lake defines a set of builtin target types -- [Lean libraries](#lean-libraries), [binary executables](#binary-executables), and [external libraries](#external-libraries) -- but a user can [define their own custom targets as well](#custom-targets). Complex types (e.g., packages, libraries, modules) have multiple facets, each of which count as separate buildable targets. See the [Defining Build Targets section](#defining-build-targets) for more details.

* A **facet** is an element built from another organizational unit (e.g., a package, module, library, etc.). For instance, Lake produces `olean`, `ilean`, `c`, and `o` files all from a single module. Each of these components are thus termed a *facet* of the module. Similarly, Lake can build both static and shared binaries from a library. Thus, libraries have both `static` and `shared` facets. Lake also allows users to define their own custom facets to build from modules and packages, but this feature is currently experimental and not yet documented.

* A **trace** is a piece of data (generally a hash) which is used to verify whether a given target is up-to-date (i.e., does not not need to be rebuilt). If the trace stored with a built target matches the trace computed during build, then a target is considered up-to-date. A target's trace is derived from its various **inputs** (e.g., source file, Lean toolchain, imports, etc.).

## Package Configuration Options

Lake provides a large assortment of configuration options for packages.

### Layout

* `packagesDir`: The directory to which Lake should download remote dependencies. Defaults to `.lake/packages`.
* `srcDir`: The directory containing the package's Lean source files. Defaults to the package's directory. (This will be passed to `lean` as the `-R` option.)
* `buildDir`: The directory to which Lake should output the package's build results. Defaults to `build`.
* `leanLibDir`: The build subdirectory to which Lake should output the package's binary Lean libraries (e.g., `.olean`, `.ilean` files). Defaults to `lib`.
* `nativeLibDir`: The build subdirectory to which Lake should output the package's native libraries (e.g., `.a`, `.so`, `.dll` files). Defaults to `lib`.
* `binDir`: The build subdirectory to which Lake should output the package's binary executables. Defaults to `bin`.
* `irDir`: The build subdirectory to which Lake should output the package's intermediary results (e.g., `.c`, `.o` files). Defaults to `ir`.

### Build & Run

* `postUpdate?`: A post-`lake update` hook. The monadic action is run after a successful `lake update` execution on this package or one of its downstream dependents. Defaults to `none`. See the option's docstring for a complete example.
* `precompileModules`:  Whether to compile each module into a native shared library that is loaded whenever the module is imported. This speeds up the evaluation of metaprograms and enables the interpreter to run functions marked `@[extern]`. Defaults to `false`.
* `moreServerOptions`: An `Array` of additional options to pass to the Lean language server (i.e., `lean --server`) launched by `lake serve`.
* `moreGlobalServerArgs`: An `Array` of additional arguments to pass to `lean --server` which apply both to this package and anything else in the same server session (e.g. when browsing other packages from the same session via go-to-definition)
* `buildType`: The `BuildType` of targets in the package (see [`CMAKE_BUILD_TYPE`](https://stackoverflow.com/a/59314670)). One of `debug`, `relWithDebInfo`, `minSizeRel`, or `release`. Defaults to `release`.
* `leanOptions`: Additional options to pass to both the Lean language server (i.e., `lean --server`) launched by `lake serve` and to `lean` while compiling Lean source files.
* `moreLeanArgs`: An `Array` of additional arguments to pass to `lean` while compiling Lean source files.
* `weakLeanArgs`: An `Array` of additional arguments to pass to `lean` while compiling Lean source files. Unlike `moreLeanArgs`, these arguments do not affect the trace of the build result, so they can be changed without triggering a rebuild. They come *before* `moreLeanArgs`.
* `moreLeancArgs`: An `Array` of additional arguments to pass to `leanc` while compiling the C source files generated by `lean`. Lake already passes some flags based on the `buildType`, but you can change this by, for example, adding `-O0` and `-UNDEBUG`.
* `weakLeancArgs`: An `Array` of additional arguments to pass to `leanc` while compiling the C source files generated by `lean`. Unlike `moreLeancArgs`, these arguments do not affect the trace of the build result, so they can be changed without triggering a rebuild. They come *before* `moreLeancArgs`.
* `moreLinkArgs`: An `Array` of additional arguments to pass to `leanc` when linking (e.g., binary executables or shared libraries). These will come *after* the paths of `extern_lib` targets.
* `weakLinkArgs`: An `Array` of additional arguments to pass to `leanc` when linking (e.g., binary executables or shared libraries) Unlike `moreLinkArgs`, these arguments do not affect the trace of the build result, so they can be changed without triggering a rebuild. They come *before* `moreLinkArgs`.
* `extraDepTargets`: An `Array` of [target](#custom-targets) names that the package should always build before anything else.

### Cloud Releases

* `releaseRepo?`: The optional URL of the GitHub repository to upload and download releases of this package.  If `none` (the default), for downloads, Lake uses the URL the package was download from (if it is a dependency) and for uploads, uses `gh`'s default.
* `buildArchive?`: The name of the build archive on GitHub. Defaults to `none`.
The archive's full file name will end up being `nameToArchive buildArchive?`.
* `preferReleaseBuild`: Whether to prefer downloading a prebuilt release (from GitHub) rather than building this package from the source when this package is used as a dependency.

## Defining Build Targets

A Lake package can have many build targets, such as different Lean libraries and multiple binary executables. Any number of these declarations can be marked with the `@[default_target]` attribute to tell Lake to build them on a bare `lake build` of the package.

### Lean Libraries

A Lean library target defines a set of Lean modules available to `import` and how to build them.

**Syntax**

```lean
lean_lib «target-name» where
  -- configuration options go here
```

**Configuration Options**

* `srcDir`: The subdirectory of the package's source directory containing the library's source files. Defaults to the package's `srcDir`. (This will be passed to `lean` as the `-R` option.)
* `roots`: An `Array` of root module `Name`(s) of the library. Submodules of these roots (e.g., `Lib.Foo` of `Lib`) are considered part of the library. Defaults to a single root of the target's name.
* `globs`: An `Array` of module `Glob`(s) to build for the library. The term `glob` comes from [file globs](https://en.wikipedia.org/wiki/Glob_(programming)) (e.g., `foo/*`) on Unix. A submodule glob builds every Lean source file within the module's directory (i.e., ``Glob.submodules `Foo`` is essentially equivalent to a theoretical `import Foo.*`). Local imports of glob'ed files (i.e., fellow modules of the workspace) are also recursively built. Defaults to a `Glob.one` of each of the library's  `roots`.
* `libName`: The `String` name of the library. Used as a base for the file names of its static and dynamic binaries. Defaults to the name of the target.
* `extraDepTargets`: An `Array` of [target](#custom-targets) names to build before the library's modules.
* `defaultFacets`: An `Array` of library facets to build on a bare `lake build` of the library. For example, setting this to `#[LeanLib.sharedLib]` will build the shared library facet.
* `nativeFacets`: An `Array` of [module facets](#defining-new-facets) to build and combine into the library's static and shared libraries. Defaults to ``#[Module.oFacet]`` (i.e., the object file compiled from the Lean source).
* `precompileModules`, `buildType`, `leanOptions`, `<more|weak><Lean|Leanc|Link>Args`, `moreServerOptions`: Augments the package's corresponding configuration option. The library's arguments come after, modules are precompiled if either the library or package are precompiled, and the build type is the minimum of the two (`debug` is the lowest, and `release` is the highest)

### Binary Executables

A Lean executable target builds a binary executable from a Lean module with a `main` function.

**Syntax**

```lean
lean_exe «target-name» where
  -- configuration options go here
```

**Configuration Options**

* `srcDir`: The subdirectory of the package's source directory containing the executable's source file. Defaults to the package's `srcDir`. (This will be passed to `lean` as the `-R` option.)
* `root`: The root module `Name` of the binary executable. Should include a `main` definition that will serve as the entry point of the program. The root is built by recursively building its local imports (i.e., fellow modules of the workspace). Defaults to the name of the target.
* `exeName`: The `String` name of the binary executable. Defaults to the target name with any `.` replaced with a `-`.
* `extraDepTargets`: An `Array` of [target](#custom-targets) names to build before the executable's modules.
* `nativeFacets`: An `Array` of [module facets](#defining-new-facets) to build and combine into the executable. Defaults to ``#[Module.oFacet]`` (i.e., the object file compiled from the Lean source).
* `supportInterpreter`: Whether to expose symbols within the executable to the Lean interpreter. This allows the executable to interpret Lean files (e.g., via `Lean.Elab.runFrontend`). Implementation-wise, this passes `-rdynamic` to the linker when building on a non-Windows systems. Defaults to `false`.
* `precompileModules`, `buildType`, `<more|weak><Lean|Leanc|Link>Args`, `moreServerOptions`: Augments the package's corresponding configuration option. The executable's arguments come after and the build type is the minimum of the two (`debug` is the lowest, and `release` is the highest).

### External Libraries

A external library target is a non-Lean **static** library that will be linked to the binaries of the package and its dependents (e.g., their shared libraries and executables).

**Important:** For the external library to link properly when `precompileModules` is on, the static library produced by an `extern_lib` target must following the platform's naming conventions for libraries (i.e., be named `foo.a` on Windows and `libfoo.a` on Unix). To make this easy, there is the `Lake.nameToStaticLib` utility function to convert a library name into its proper file name for the platform.

**Syntax**

```lean
extern_lib «target-name» (pkg : NPackage _package.name) :=
  -- a build function that produces its static library
```

The declaration is essentially a wrapper around a `System.FilePath` [target](#custom-targets). Like such a target, the `pkg` parameter and its type specifier are optional and body should be a term of type `IndexBuildM (BuildJob System.FilePath)` function that builds the static library. The `pkg` parameter is of type `NPackage _package.name` to provably demonstrate that it is the package in which the external library is defined.

### Custom Targets

A arbitrary target that can be built via `lake build <target-name>`.

**Syntax**

```lean
target «target-name» (pkg : NPackage _package.name) : α :=
  -- a build function that produces a `BuildJob α`
```

The `pkg` parameter and its type specifier are optional and the body should be a term of type `IndexBuildM (BuildJob α)`. The `pkg` parameter is of type `NPackage _package.name` to provably demonstrate that it is the package in which the target is defined.

## Defining New Facets

A Lake package can also define new *facets* for packages, modules, and libraries. Once defined, the new facet (e.g., `facet`) can be built on any current or future object of its type (e.g., through `lake build pkg:facet` for a package facet). Module facets can also be provided to [`LeanLib.nativeFacets`](#lean-libraries) to have Lake build and use them automatically when producing shared libraries.

**Syntax**

```lean
package_facet «facet-name» (pkg : Package) : α :=
  -- a build function that produces a `BuildJob α`

module_facet «facet-name» (mod : Module) : α :=
  -- a build function that produces a `BuildJob α`

library_facet «facet-name» (lib : LeanLib) : α :=
  -- a build function that produces a `BuildJob α`
```

In all of these, the object parameter and its type specifier are optional and the body should be a term of type `IndexBuildM (BuildJob α)`.

## Adding Dependencies

Lake packages can have dependencies. Dependencies are other Lake packages the current package needs in order to function. They can be sourced directly from a local folder (e.g., a subdirectory of the package) or come from remote Git repositories. For example, one can depend on [mathlib](https://github.com/leanprover-community/mathlib4) like so:

```lean
package hello

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
```

The next run of `lake build` (or refreshing dependencies in an editor like VSCode) will clone the mathlib repository and build it. Information on the specific revision cloned will then be saved to `lake-manifest.json` to enable reproducibility (i.e., ensure the same version of mathlib is used by future builds). To update `mathlib` after this, you will need to run `lake update` -- other commands do not update resolved dependencies.

For theorem proving packages which depend on `mathlib`, you can also run `lake new <package-name> math` to generate a package configuration file that already has the `mathlib` dependency (and no binary executable target).

**NOTE:** For mathlib in particular, you should run `lake exe cache get` prior to a `lake build` after adding or updating a mathlib dependency. Otherwise, it will be rebuilt from scratch (which can take hours). For more information, see mathlib's [wiki page](https://github.com/leanprover-community/mathlib4/wiki/Using-mathlib4-as-a-dependency) on using it as a dependency.

### Syntax of `require`

The `require` command has two forms:

```lean
require foo from "path"/"to"/"local"/"package" with NameMap.empty
require bar from git "url.git"@"rev"/"optional"/"path-to"/"dir-with-pkg"
```

The first form adds a local dependency and the second form adds a Git dependency. For a Git dependency, the revision can be a commit hash, branch, or tag. Also, the `@"rev"` and `/"path-to"/"term"` parts of the `require` are optional.

Both forms also support an optional `with` clause to specify arguments to pass to the dependency's package configuration (i.e., same as `args` in a `lake build -- <args...>` invocation). The elements of both the `from` and `with` clauses are proper terms so normal computation is supported within them (though parentheses made be required to disambiguate the syntax).

## GitHub Release Builds

Lake supports uploading and downloading build artifacts (i.e., the archived build directory) to/from the GitHub releases of packages. This enables end users to fetch pre-built artifacts from the cloud without needed to rebuild the package from the source themselves.

### Downloading

To download artifacts, one should configure the package [options](#cloud-releases) `releaseRepo?` and `buildArchive?` as necessary to point to the GitHub repository hosting the release and the correct artifact name within it (if the defaults are not sufficient). Then, set `preferReleaseBuild := true` to tell Lake to fetch and unpack it as an extra package dependency.

Lake will only fetch release builds as part of its standard build process if the package wanting it is a dependency (as the root package is expected to modified and thus not often compatible with this scheme). However, should one wish to fetch a release for a root package (e.g., after cloning the release's source but before editing), one can manually do so via `lake build :release`.

Lake internally uses `curl` to download the release and `tar` to unpack it, so the end user must have both tools installed to use this feature. If Lake fails to fetch a release for any reason, it will move on to building from the source. Also note that this mechanism is not technically limited to GitHub, any Git host that uses the same URL scheme works as well.

### Uploading

To upload a built package as an artifact to a GitHub release, Lake provides the `lake upload <tag>` command as a convenient shorthand. This command uses `tar` to pack the package's build directory into an archive and uses `gh release upload` to attach it to a pre-existing GitHub release for `tag`. Thus, in order to use it, the package uploader (but not the downloader) needs to have `gh`, the [GitHub CLI](https://cli.github.com/), installed and in `PATH`.

## Writing and Running Scripts

A configuration file can also contain a number of `scripts` declaration. A script is an arbitrary `(args : List String) → ScriptM UInt32` definition that can be run by `lake script run`. For example, given the following `lakefile.lean`:

```lean
import Lake
open Lake DSL

package scripts

/--
Display a greeting

USAGE:
  lake run greet [name]

Greet the entity with the given name. Otherwise, greet the whole world.
-/
script greet (args) do
  if h : 0 < args.length then
    IO.println s!"Hello, {args[0]'h}!"
  else
    IO.println "Hello, world!"
  return 0
```

The script `greet` can be run like so:

```
$ lake script run greet
Hello, world!
$ lake script run greet me
Hello, me!
```

You can print the docstring of a script with `lake script doc`:

```
$ lake script doc greet
Display a greeting

USAGE:
  lake run greet [name]

Greet the entity with the given name. Otherwise, greet the whole world.
```

## Building and Running Lake from the Source

If you already have a Lean installation with `lake` packaged with it, you can build a new `lake` by just running `lake build`.

Otherwise, there is a pre-packaged `build.sh` shell script that can be used to build Lake. It passes it arguments down to a `make` command. So, if you have more than one core, you will probably want to use a `-jX` option to specify how many build tasks you want it to run in parallel. For example:

```shell
$ ./build.sh -j4
```

After building, the `lake` binary will be located at `.lake/build/bin/lake` and the library's `.olean` files will be located in `.lake/build/lib`.

### Building with Nix Flakes

Lake is built as part of the main Lean 4 flake at the repository root.

### Augmenting Lake's Search Path

The `lake` executable needs to know where to find the Lean library files (e.g., `.olean`, `.ilean`) for the modules used in the package configuration file (and their source files for go-to-definition support in the editor). Lake will intelligently setup an initial search path based on the location of its own executable and `lean`.

Specifically, if Lake is co-located with `lean` (i.e., there is `lean` executable in the same directory as itself), it will assume it was installed with Lean and that both Lean and Lake are located under their shared sysroot. In particular, their binaries are located in `<sysroot>/bin`, their Lean libraries in `<sysroot>/lib/lean`, Lean's source files in `<sysroot>/src/lean`, and Lake's source files in `<sysroot>/src/lean/lake`. Otherwise, it will run `lean --print-prefix` to find Lean's sysroot and assume that Lean's files are located as aforementioned, but that `lake` is at `<lake-home>/.lake/build/bin/lake` with its Lean libraries at `<lake-home>/.lake/build/lib` and its sources directly in `<lake-home>`.

This search path can be augmented by including other directories of Lean libraries in the `LEAN_PATH` environment variable (and their sources in `LEAN_SRC_PATH`). This can allow the user to correct Lake's search when the files for Lean (or Lake itself) are in non-standard locations. However, such directories will *not* take precedence over the initial search path. This is important during development, as this prevents the Lake version used to build Lake from using the Lake version being built's Lean libraries (instead of its own) to elaborate Lake's `lakefile.lean` (which can lead to all kinds of errors).
