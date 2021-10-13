# Lake

Lake (Lean Make) is a new build system and package manager for Lean 4.
With Lake, package configuration is written in Lean inside a dedicated `lakefile.lean` stored in the root of the package directory. Each `lakefile.lean` includes a `package` declaration (akin to `main`) which defines the package's configuration.

## Building and Running Lake

As Lake functions as an alternative to `leanpkg`, it is not built with it. Instead, there is a pre-packaged `build.sh` shell script which is used to build Lake. It passes it arguments down to a `make` command. So, if you have more than one core, you will probably want to use a `-jX` option to specify how many build tasks you want it to run in parallel. For example:

```shell
$ ./build.sh -j4
```

After building, the `lake` binary will be located at `build/bin/lake` and the library's `.olean` files will be located directly in `build`.

### Building with Nix Flakes

It is also possible to build Lake with the Nix setup `buildLeanPackage` from the [`leanprover/lean4`](https://github.com/leanprover/lean4) repository. To do so, you need to have Nix installed with flakes enabled. It is recommended to also set up the Lean 4 binary cache as described in the Lean 4 repository.

It is then possible to build Lake with `nix build .` or run it from anywhere with `nix run github:leanprover/lake`.

A development environment with Lean 4 installed can be loaded automatically by running `nix develop` or automatically on `cd` with `direnv` by running `direnv allow`.

The versions of `nixpkgs` and `lean4` are fixed to specific hashes. They can be updated by running `nix flake update`.

Thank Anders Christiansen Sørby ([@Anderssorby](https://github.com/Anderssorby)) for this support!

### Augmenting Lake's Search Path

The `lake` executable needs to know where to find the `.olean` files for the modules used in the package configuration file. Lake will intelligently setup an initial search path based on the location of its own executable and `lean`.

Specifically, if Lake is co-located with `lean` (i.e., there is `lean` executable in the same directory as itself), it will assume it was installed with Lean and that both Lean and Lake are located in `<lean-home>/bin` with Lean's `.olean` files at `<lean-home/lib/lean` and Lake's at `.olean` files at `<lean-home/lib/lake`. Otherwise, it will run `lean --print-prefix` to find Lean's home and assume that its `.olean` files are at `<lean-home>/lib/lean` and that `lake` is at `<lake-home>/bin/lake` with its `.olean` files at `<lake-home>`.

This search path can be augmented by including other directories of `.olean` files in the `LEAN_PATH` environment variable. Such directories will take precedence over the initial search path, so `LEAN_PATH` can also be used to correct Lake's search if the `.olean` files for Lean (or Lake itself) are in non-standard locations.

## Creating and Building a Package

We can set up a new package by running `lake init <package-name>` in a fresh directory. For example, we can create the package `hello` like so:

```
$ mkdir hello
$ cd hello
$ lake init hello
```

This will initialize a git repository in the directory with a basic `.gitignore` that ignores the build directory (i.e., `build`) where Lake outputs build files.

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

## Configuration Options

Lake provides a large assortment of configuration options for packages.

### Workspace

Workspace options are shared across a package and its dependencies.

* `depsDir`: The directory to which Lake should download dependencies. Defaults to `lean_packages`.

### General

* `name` **(Required)**: The `Name` of the package.
* `dependencies`: An `Array` of the package's dependencies.
* `extraDepTarget`: An extra `OpaqueTarget` that should be built before the package. `OpaqueTarget.collectList/collectArray` can be used combine multiple extra targets into a single `extraDepTarget`.
* `defaultFacet`: The `PackageFacet` to build on a bare `lake build` of the package. Can be one of `bin`, `staticLib`, or `oleans`. Defaults to `bin`. See `lake help build` for more info on build facets.
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
* `moreLinkArgs`: An `Array` of additional arguments to pass to `leanc` while compiling the package's binary executable. These will come *after* the paths of libraries built with `moreLibTargets`.

## Scripts

A configuration file can also contain a number of `scripts` declaration. A script is an arbitrary `(args : List String) → IO UInt32` definition that can be run by `lake run <script> [-- <args>]`. For example, given the following `lakefile.lean`:

```lean
import Lake
open Lake DSL

package scripts

script greet (args) do
  if h : 0 < args.length then
    IO.println s!"Hello, {args.get 0 h}!"
  else
    IO.println "Hello, world!"
  return 0
```

The script `greet` can be run like so:
```
$ lake run greet
Hello, world!
$ lake run greet -- me
Hello, me!
```
