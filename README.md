# Lake

Lake (Lean Make) is a new build system and package manager for Lean 4.
With Lake, the package's configuration is written in Lean inside a dedicated `lakefile.lean` stored in the root of the package's directory.

Each `lakefile.lean` includes a `package` declaration (akin to `main`) which defines the package's basic configuration. It also typically includes build configurations for different targets (e.g., Lean libraries and binary executables) and Lean scripts to run on the command line (via `lake script run`).

***This README provides information about Lake relative to the current commit. If you are looking for documentation for the Lake version shipped with a given Lean nightly, you should look at the README of that version.***

## Table of Contents

* [Getting Lake](#getting-lake)
* [Creating and Building a Package](#creating-and-building-a-package)
* [Package Configuration Options](#package-configuration-options)
* [Defining Build Targets](#defining-build-targets)
  + [Lean Libraries](#lean-libraries)
  + [Binary Executables](#binary-executables)
  + [External Libraries](#external-libraries)
  + [Custom Targets](#custom-targets)
* [Adding Dependencies](#adding-dependencies)
  + [Syntax of `require`](#syntax-of-require)
* [Writing and Running Scripts](#writing-and-running-scripts)
* [Building and Running Lake from the Source](#building-and-running-lake-from-the-source)
  + [Building with Nix Flakes](#building-with-nix-flakes)
  + [Augmenting Lake's Search Path](#augmenting-lakes-search-path)

## Getting Lake

Lake is part of the [lean4](https://github.com/leanprover/lean4) repository and is distributed along with its official releases (e.g., as part of the [elan](https://github.com/leanprover/elan) toolchain). So if you have installed a semi-recent Lean 4 nightly, you should already have it!

Note that the Lake included with Lean is not updated as frequently as this repository, so some bleeding edge features may be missing. If you want to build the latest version from the source yourself, check out the [build instructions](#building-and-running-lake-from-the-source) at the bottom of this README.

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

Either way, Lake will initialize a git repository in the package directory with a basic `.gitignore` that ignores the build directory (i.e., `build`) where Lake outputs build files.

It will also create the root Lean file for the package's library, which uses the capitalized version of the package's name (e.g., `Hello.lean` in this example), and the root file for the package's binary `Main.lean`. They contain the following dummy "Hello World" program split across the two files:

**Hello.lean**
```lean
def hello := "world"
```

**Main.lean**
```lean
import Hello

def main : IO Unit :=
  IO.println s!"Hello, {hello}!"
```

Lake also creates a basic `lakefile.lean` for the package along with a `lean-toolchain` file that contains the version string of the currently active Lean, which tells [`elan`](https://github.com/leanprover/elan) to use that Lean toolchain for the package.


**lakefile.lean**
```lean
import Lake
open Lake DSL

package hello {
  -- add package configuration options here
}

lean_lib Hello {
  -- add library configuration options here
}

@[defaultTarget]
lean_exe hello {
  root := `Main
}
```

The command `lake build` can then be used to build the package (and its [dependencies](#adding-dependencies), if it has them) into a native executable. The result will be placed in `build/bin`.

```
$ lake build
...
$ ./build/bin/hello
Hello, world!
```

Examples of different package configurations can be found in the [`examples`](examples) folder of this repository. You can also specified a particular configuration file template when using `lake init` or `lake new` to control what files Lake creates. See `lake help init` or `lake help new` for details.

## Package Configuration Options

Lake provides a large assortment of configuration options for packages.

**Workspace Options**

Workspace options are shared across a package and its dependencies.

* `packagesDir`: The directory to which Lake should download remote dependencies. Defaults to `lean_packages`.

**Per Package Options**

* `srcDir`: The directory containing the package's Lean source files. Defaults to the package's directory. (This will be passed to `lean` as the `-R` option.)
* `buildDir`: The directory to which Lake should output the package's build results. Defaults to `build`.
* `oleanDir`: The build subdirectory to which Lake should output the package's `.olean` files. Defaults to `lib`.
* `irDir`: The build subdirectory to which Lake should output the package's intermediary results (e.g., `.c` and `.o` files). Defaults to `ir`.
* `libDir`: The build subdirectory to which Lake should output the package's libraries. Defaults to `lib`.
* `binDir`: The build subdirectory to which Lake should output the package's binary executables. Defaults to `bin`.
* `precompileModules`:  Whether to compile each module into a native shared library that is loaded whenever the module is imported. This speeds up the evaluation of metaprograms and enables the interpreter to run functions marked `@[extern]`. Defaults to `false`.
* `isLeanOnly`: Whether the package is "Lean-only". A Lean-only package does not produce native files for modules (e.g. `.c`, `.o`). Defaults to `false`. Setting `precompileModules` to `true` will override this setting and produce native files anyway (as they are needed to build module dynlibs).
* `moreServerArgs`:  Additional arguments to pass to the Lean language server (i.e., `lean --server`) launched by `lake serve`.
* `buildType`: The `BuildType` of targets in the package (see [`CMAKE_BUILD_TYPE`](https://stackoverflow.com/a/59314670)). One of `debug`, `relWithDebInfo`, `minSizeRel`, or `release`. Defaults to `release`.
* `moreLeanArgs`: An `Array` of additional arguments to pass to `lean` while compiling Lean source files.
* `moreLeancArgs`: An `Array` of additional arguments to pass to `leanc` while compiling the C source files generated by `lean`. Lake already passes some flags based on the `buildType`, but you can change this by, for example, adding `-O0` and `-UNDEBUG`.
* `moreLinkArgs`: An `Array` of additional arguments to pass to `leanc` when linking (e.g., binary executables or shared libraries). These will come *after* the paths of `extern_lib` targets.
* `extraDepTarget`: An extra `OpaqueTarget` that should be built before the package. `Target.collectOpaqueList/collectOpaqueArray` can be used combine multiple extra targets into a single `extraDepTarget`. **DEPRECATED:** Try to use separate [custom target declarations](#custom-targets) instead. Otherwise, raise an issue here about your use case.

## Defining Build Targets

A Lake package can have many build targets, such as different Lean libraries and multiple binary executables. Any number of these declarations can be marked with the `@[defaultTarget]` attribute to tell Lake to build them on a bare `lake build` of the package.

### Lean Libraries

A Lean library target defines a set of Lean modules available to `import` and how to build them.

**Syntax**

```lean
lean_lib «target-name» {
  -- configuration options go here
}
```

**Configuration Options**

* `roots`: The root module(s) of the library. Submodules of these roots (e.g., `Lib.Foo` of `Lib`) are considered part of the library. Defaults to a single root of the library's upper camel case name.
* `globs`: An `Array` of module `Glob`s to build for the library. Defaults to a `Glob.one` of each of the library's  `roots`. Submodule globs build every source file within their directory. Local imports of glob'ed files (i.e., fellow modules of the workspace) are also recursively built.
* `libName`: The name of the library. Used as a base for the file names of its static and dynamic binaries. Defaults to the upper camel case name of the target.
* `nativeFacets`: An `Array` of module facets to build and combine into the library's static
and shared libraries. Defaults to ``#[Module.oFacet]`` (i.e., the object file compiled from the Lean source). **PREVIEW:** Module facets are in beta, unstable, and not yet documented. Use with care.
* `precompileModules`, `buildType`, `moreLeanArgs`, `moreLinkArgs`, `moreLinkArgs`: Augments the package's corresponding configuration option. The library's arguments come after, modules are precompiled if either the library or package are precompiled, and the build type is the minimum of the two (`debug` is the lowest, and `release` is the highest)

### Binary Executables

A Lean executable target builds a binary executable from a Lean module with a `main` function.

**Syntax**

```lean
lean_exe «target-name» {
  -- configuration options go here
}
```

**Configuration Options**

* `root`: The root module of the binary executable. Should include a `main` definition that will serve as the entry point of the program. The root is built by recursively building its local imports (i.e., fellow modules of the workspace). Defaults to the name of the target.
* `exeName`: The name of the binary executable. Defaults to the target name with any `.` replaced with a `-`.
* `supportInterpreter`: Whether to expose symbols within the executable to the Lean interpreter. This allows the executable to interpret Lean files (e.g., via `Lean.Elab.runFrontend`). Implementation-wise, this passes `-rdynamic` to the linker when building on a non-Windows systems. Defaults to `false`.
* `buildType`, `moreLeanArgs`, `moreLinkArgs`, `moreLinkArgs`: Augments the package's corresponding configuration option. The executable's arguments come after and the build type is the minimum of the two (`debug` is the lowest, and `release` is the highest).

### External Libraries

A external library target is a non-Lean **static** library that will be linked to the binaries of the package and its dependents (e.g., their shared libraries and executables).

**Important:** For the external library to link properly when `precompileModules` is on, the static library produced by an `extern_lib` target must following the platform's naming conventions for libraries (i.e., be named `foo.a` on Windows and `libfoo.a` on Unix). To make this easy, there is the `Lake.nameToStaticLib` utility function to convert a library name into its proper file name for the platform.

**Syntax**

```lean
extern_lib «target-name» :=
  -- term of type `FileTarget` that builds the external library
```

### Custom Targets

A arbitrary target that can be built via `lake build <target-name>`.

**Syntax**

```lean
target «target-name» : α :=
  -- term of type `BuildTarget α` that builds the target
```

## Adding Dependencies

Lake packages can have dependencies. Dependencies are other Lake packages the current package needs in order to function. They can be sourced directly from a local folder (e.g., a subdirectory of the package) or come from remote Git repositories. For example, one can depend on the Lean 4 port of [mathlib](https://github.com/leanprover-community/mathlib4) like so:

```lean
package hello

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
```

The next run of `lake build` (or refreshing dependencies in an editor like VSCode) will clone the mathlib repository and build it. Information on the specific revision cloned will then be saved to `manifest.json` in the workspace's `packageDir` (by default, `lean_packages`) to enable reproducibility. To update `mathlib` after this, you will need to run `lake update` -- other commands do not update resolved dependencies.

For a theorem proving packages which depend on `mathlib`, you can also run `lake new <package-name> math` to generate a package configuration file that already has the `mathlib` dependency (and no binary executable target).

### Syntax of `require`

The `require` command has two forms:

```lean
require foo from "path"/"to"/"local"/"package" with ["optional","args"]
require bar from git "url.git"@"rev"/"optional"/"path-to"/"dir-with-pkg"
```

The first form adds a local dependency and the second form adds a Git dependency. For a Git dependency, the revision can be a commit hash, branch, or tag. Also, the `@"rev"` and `/"path-to"/"term"` parts of the `require` are optional.

Both forms also support an optional `with` clause to specify arguments to pass to the dependency's package configuration (i.e., same as `args` in a `lake build -- <args...>` invocation). The elements of both the `from` and `with` clauses are proper terms so normal computation is supported within them (though parentheses made be required to disambiguate the syntax).

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
    IO.println s!"Hello, {args.get 0 h}!"
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

After building, the `lake` binary will be located at `build/bin/lake` and the library's `.olean` files will be located in `build/lib`.

### Building with Nix Flakes

It is also possible to build Lake with the Nix setup `buildLeanPackage` from the [`lean4`](https://github.com/leanprover/lean4) repository. To do so, you need to have Nix installed with flakes enabled. It is recommended to also set up the Lean 4 binary cache as described in the Lean 4 repository.

It is then possible to build Lake with `nix build .` or run it from anywhere with `nix run github:leanprover/lake`.

A development environment with Lean 4 installed can be loaded automatically by running `nix develop` or automatically on `cd` with `direnv` by running `direnv allow`.

The versions of `nixpkgs` and `lean4` are fixed to specific hashes. They can be updated by running `nix flake update`.

Thank Anders Christiansen Sørby ([@Anderssorby](https://github.com/Anderssorby)) for this support!

### Augmenting Lake's Search Path

The `lake` executable needs to know where to find the Lean library files (e.g., `.olean`. `.ilean`) for the modules used in the package configuration file (and their source files for go-to-definition support in the editor). Lake will intelligently setup an initial search path based on the location of its own executable and `lean`.

Specifically, if Lake is co-located with `lean` (i.e., there is `lean` executable in the same directory as itself), it will assume it was installed with Lean and that both Lean and Lake are located under their shared sysroot. In particular, their binaries are located in `<sysroot>/bin`, their Lean libraries in `<sysroot>/lib/lean`, Lean's source files in `<sysroot>/src/lean`, and Lake's source files in `<sysroot>/src/lean/lake`. Otherwise, it will run `lean --print-prefix` to find Lean's sysroot and assume that Lean's files are located as aforementioned, but that `lake` is at `<lake-home>/build/bin/lake` with its Lean libraries at `<lake-home>/build/lib` and its sources in directly in `<lake-home>`.

This search path can be augmented by including other directories of Lean libraries in the `LEAN_PATH` environment variable (and their sources in `LEAN_SRC_PATH`), allowing the user to correct Lake's search if the files for Lean (or Lake itself) are in non-standard locations. However, such directories will *not* take precedence over the initial search path. This is important in development, as it prevents the Lake version being used to build Lake from using the Lake version being built's Lean libraries to elaborate Lake's `lakefile.lean` (which can lead to all kinds of errors).
