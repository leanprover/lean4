# Lake

Lake (Lean Make) is a new build system and package manager for Lean 4.
With Lake, package configuration is written in Lean inside a dedicated `package.lean` file stored in the root of the package directory. Each `package.lean` includes a `package` definition (akin to `main`) which defines the package's configuration.

## Building and Running Lake

As Lake functions as an alternative to `leanpkg`, it is not built with it. Instead, there is a pre-packaged `build.sh` shell script which is used to build Lake. It passes it arguments down to a `make` command. So, if you have more than one core, you will probably want to use a `-jX` option to specify how many build tasks you want it to run in parallel. For example:

```shell
$ ./build.sh -j4
```

After building, the `lake` binary will be located at `build/bin/lake` and the library's `.olean` files will be located directly in `build`.

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

It will also create the root Lean file for the package, which uses the capitalized version of the package's name (e.g., `Hello.lean` in this example). It contains the following dummy "Hello World" program:

```lean
def main : IO Unit :=
  IO.println "Hello, world!"
```

Lake also creates a basic `package.lean` for the package:

```lean
import Lake.Package

def package : Lake.PackageConfig := {
  name := "hello"
  version := "0.1"
}
```

along with a `lean-toolchain` file that contains the version string of the currently active Lean, which tells [`elan`](https://github.com/leanprover/elan) to use that Lean toolchain for the package.

The command `lake build-bin` can then be used to build the package (and its dependencies, if it has them) into a native executable. The result will be placed in `build/bin`.

```
$ lake build-bin
...
$ ./build/bin/hello
Hello, world!
```

## Configuration Options

Lake provides a large assortment of configuration options for packages.

### General

* `name` **(Required)**: The name of the package.
* `version` **(Required)**: The version string of the package.
* `scripts`: A `HashMap` of scripts for the package. A `Script` is an arbitrary `(args : List String) → IO PUnit` function that is indexed by a `String` key and can be be run by `lake run <key> [-- <args>]`.
* `dependencies`: A `List` of the package's dependencies.
* `depsDir`: The directory to which Lake should download dependencies. Defaults to `lean_packages`.
* `extraDepTarget`: An extra `OpaqueTarget` that should be built before the package.
* `srcDir`: The directory containing the package's Lean source files. Defaults to the package's directory. (This will be passed to `lean` as the `-R` option.)
* `buildDir`: The directory to which Lake should output the package's build results. Defaults to `build`.
* `oleanDir`: The build subdirectory to which Lake should output the package's `.olean` files. Defaults to `lib`.
* `libRoots`: The root module(s) of the package. Imports relative to this root (e.g., `Pkg.Foo`) are considered part of the package. Defaults to a single root of the package's uppercase `name`.
* `libGlobs`: An `Array` of additional module `Glob`s to include in the package. Defaults to singular globs of the module's `libRoots`. Submodule globs build every source file within their directory. Local imports of said files (i.e., fellow modules of the package) are also recursively built.
* `leanArgs`: An `Array` of additional arguments to pass to `lean` while compiling Lean source files.

### Library / Binary Compilation

* `leancArgs`: An `Array` additional arguments to pass to `leanc` while compiling the C source files generated by `lean`.
* `irDir`: The build subdirectory to which Lake should output the package's intermediary results (e.g., `.c` and `.o` files). Defaults to `ir`.
* `libName`: The name of the package's static library. Defaults to the string representation of the package's `moduleRoot`.
* `libDir`: The build subdirectory to which Lake should output the package's static library. Defaults to `lib`.
* `binName`: The name of the package's binary executable. Defaults to the package's `name`.
* `binDir`: The build subdirectory to which Lake should output the package's binary executable. Defaults to `bin`.
* `binRoot`: The root module of the package's binary executable. Defaults to the package's `moduleRoot`. The root is built by recursively building its local imports (i.e., fellow modules of the package). This setting is most useful for packages that are distributing both a library and a binary (like Lake itself). In such cases, it is common for there to be code (e.g., `main`) that is needed for the binary but should not be included in the library proper.
* `moreLibTargets`: Additional library `FileTarget`s (beyond the package's and its dependencies' libraries) to build and link to the package's binary executable (and/or to dependent package's executables).
* `linkArgs`: Additional arguments to pass to `leanc` while compiling the package's binary executable. These will come *after* the paths of libraries built with `moreLibTargets`.
