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

The `lake` executable needs to know where to find the `.olean` files for the modules used in the package configuration file. Lake will intelligently setup an initial search path based on the location of its own executable and `lean`. It will assume that `lean` is located at `<lean-home>/bin/lean` with its `.olean` files (e.g., for `Init`) at `<lean-home>/lib/lean` and that `lake` is at `<lake-home>/bin/lake` with its `.olean` files at `<lake-home>`.

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
