# Lake

Lake (Lean Make) is a new build system and package manager for Lean 4.
With Lake, package configuration is written in Lean inside a dedicated `lakefile.lean` stored in the root of the package directory. Each `lakefile.lean` includes a `package` declaration (akin to `main`) which defines the package's configuration.

## Getting Lake

Lake is part of the [lean4](https://github.com/leanprover/lean4) repository and is distributed along with its official releases (e.g., as part of the [elan](https://github.com/leanprover/elan) toolchain). So if you have installed a semi-recent Lean 4 nightly, you should already have it!

Note that the Lake included with Lean is not updated as frequently as this repository, so some bleeding edge features may be missing. If you want to build the latest version from the source yourself, check out the build instructions at the bottom of this README.

## Creating and Building a Package

To create a new package, either run `lake init <package-name>` to setup the package in the current directory or `lake new <package-name>` to create it in a new directory. For example, we could create the package `hello` like so:

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
def main : IO Unit :=
  IO.println s!"Hello, {hello}!"
```

Lake also creates a basic `lakefile.lean` for the package:

```lean
import Lake
open Lake DSL

package hello {
  -- add configuration options here
}
```

along with a `lean-toolchain` file that contains the version string of the currently active Lean, which tells [`elan`](https://github.com/leanprover/elan) to use that Lean toolchain for the package.

The command `lake build` can then be used to build the package (and its dependencies, if it has them) into a native executable. The result will be placed in `build/bin`.

```
$ lake build
...
$ ./build/bin/hello
Hello, world!
```

## Adding Dependencies

Lake packages can also have dependencies. Dependencies are other Lake packages the current package needs in order to function. To define a dependency, add an entry to the `dependencies` field of the package configuration. Each entry includes the name of the package and where to find it. Dependencies can be sourced directly from a local folder (e.g., a subdirectory of the package) or come from remote Git repositories. When sourcing from a Git repository, specify the revision of the package to clone, which can be a commit hash, branch, or tag.

For example, one can depend on the Lean 4 port of [mathlib](https://github.com/leanprover-community/mathlib4) like so:

```lean
package hello {
  dependencies := #[{
    name := `mathlib
    src := Source.git "https://github.com/leanprover-community/mathlib4.git" "master"
  }]
}
```

The next run of `lake build` (or refreshing dependencies in an editor like VSCode) will clone the mathlib repository and build it. Information on the specific revision cloned will then be saved to `manifest.json` in `lean_packages` to enable reproducibility. To update `mathlib` after this, you will need to run `lake update` -- other commands do not update resolved dependencies.

Further examples of different package configurations can be found in the [`examples`](examples) folder of this repository.

## Package Configuration Options

Lake provides a large assortment of configuration options for packages.

### Workspace

Workspace options are shared across a package and its dependencies.

* `packagesDir`: The directory to which Lake should download remote dependencies. Defaults to `lean_packages`.

### General

* `dependencies`: An `Array` of the package's dependencies.
* `extraDepTarget`: An extra `OpaqueTarget` that should be built before the package. `Target.collectOpaqueList/collectOpaqueArray` can be used combine multiple extra targets into a single `extraDepTarget`.
* `defaultFacet`: The `PackageFacet` to build on a bare `lake build` of the package. Can be one of `bin`, `staticLib`, `sharedLib`, or `oleans`. Defaults to `bin`. See `lake help build` for more info on build facets.
* `moreServerArgs`:  Additional arguments to pass to the Lean language server (i.e., `lean --server`) launched by `lake server`.
* `srcDir`: The directory containing the package's Lean source files. Defaults to the package's directory. (This will be passed to `lean` as the `-R` option.)
* `buildDir`: The directory to which Lake should output the package's build results. Defaults to `build`.
* `oleanDir`: The build subdirectory to which Lake should output the package's `.olean` files. Defaults to `lib`.
* `libRoots`: The root module(s) of the package. Imports relative to this root (e.g., `Pkg.Foo`) are considered part of the package. Defaults to a single root of the package's uppercase `name`.
* `libGlobs`: An `Array` of module `Glob`s to build for the package's library. Defaults to a `Glob.one` of each of the module's `libRoots`. Submodule globs build every source file within their directory. Local imports of glob'ed files (i.e., fellow modules of the package) are also recursively built.
* `moreLeanArgs`: An `Array` of additional arguments to pass to `lean` while compiling Lean source files.

### Library / Binary Compilation

* `moreLeancArgs`: An `Array` of additional arguments to pass to `leanc` while compiling the C source files generated by `lean`. Lake already passes `-O3` and `-DNDEBUG` automatically, but you can change this by, for example, adding `-O0` and `-UNDEBUG`.
* `irDir`: The build subdirectory to which Lake should output the package's intermediary results (e.g., `.c` and `.o` files). Defaults to `ir`.
* `libName`: The name of the package's static library. Defaults to the package's upper camel case `name`.
* `libDir`: The build subdirectory to which Lake should output the package's static library. Defaults to `lib`.
* `binName`: The name of the package's binary executable. Defaults to the package's `name` with any `.` replaced with a `-`.
* `binDir`: The build subdirectory to which Lake should output the package's binary executable. Defaults to `bin`.
* `binRoot`: The root module of the package's binary executable. Defaults to `Main`. The root is built by recursively building its local imports (i.e., fellow modules of the package). This setting is most useful for packages that are distributing both a library and a binary (like Lake itself). In such cases, it is common for there to be code (e.g., `main`) that is needed for the binary but should not be included in the library proper.
* `moreLibTargets`: An `Array` of additional library `FileTarget`s (beyond the package's and its dependencies' libraries) to build and link to the package's binary executable (and/or to dependent package's executables).
* `supportInterpreter`: Whether to expose symbols within the executable to the Lean interpreter. This allows the executable to interpret Lean files (e.g., via `Lean.Elab.runFrontend`). Implementation-wise, this passes `-rdynamic` to the linker when building on a non-Windows systems. Defaults to `false`.
* `moreLinkArgs`: An `Array` of additional arguments to pass to `leanc` while compiling the package's binary executable. These will come *after* the paths of libraries built with `moreLibTargets`.

## Scripts

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

The `lake` executable needs to know where to find the `.olean` files for the modules used in the package configuration file. Lake will intelligently setup an initial search path based on the location of its own executable and `lean`.

Specifically, if Lake is co-located with `lean` (i.e., there is `lean` executable in the same directory as itself), it will assume it was installed with Lean and that both Lean and Lake are located in `<lean-home>/bin` with Lean's `.olean` files at `<lean-home/lib/lean` and Lake's `.olean` files at `<lean-home/lib/lean`. Otherwise, it will run `lean --print-prefix` to find Lean's home and assume that its `.olean` files are at `<lean-home>/lib/lean` and that `lake` is at `<lake-home>/bin/lake` with its `.olean` files at `<lake-home>/lib`.

This search path can be augmented by including other directories of `.olean` files in the `LEAN_PATH` environment variable. Such directories will take precedence over the initial search path, so `LEAN_PATH` can also be used to correct Lake's search if the `.olean` files for Lean (or Lake itself) are in non-standard locations.
