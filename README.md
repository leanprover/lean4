# Lake

Lake (Lean Make) is a new build system and package manager for Lean 4.
With Lake, package configuration is written in Lean inside a dedicated `package.lean` file stored in the root of the package directory. Each `package.lean` includes a `package` definition (akin to `main`) which defines the package's configuration.

## Building and Running Lake

As Lake functions as an alternative to `leanpkg`, the most direct way of building Lake is through `leanmake`. However, you can also build it with `leanpkg`. Either way, you will need to provide some additional linker options to create an executable that can correctly interpret the Lake package configuration files.

On Unix:

```
$ leanmake PKG=Lake LEAN_PATH=./build bin LINK_OPTS=-rdynamic
```

or

```
$ leanpkg build bin LINK_OPTS=-rdynamic
```

On Windows (MSYS2):

```
$ leanmake PKG=Lake LEAN_PATH=./build bin LINK_OPTS=-Wl,--export-all
```

or

```
$ leanpkg build bin LINK_OPTS=-Wl,--export-all
```

Alternatively, you can build Lake by running the the pre-packaged `build-msys2.sh` and `build-unix.sh` shell scripts, which include the `leanmake` commands.

### Augmenting Lake's Search Path

The built executable also needs to know where to find the `.olean` files for the modules used in the package configuration file. Lake will intelligently setup an initial search path based on the location of its own executable and `lean`. It will assume that `lean` is located at `<lean-home>/bin/lean` with its `.olean` files (e.g., for `Init`) at `<lean-home>/lib/lean` and that `lake` is at `<lake-home>/bin/lake` with its `.olean` files at `<lake-home>`.

You can augment this search path by including other directories of `.olean` files in the `LEAN_PATH` environment variable. Such directories will take precedence over the initial search path, so `LEAN_PATH` can also be used to correct Lake's search if the `.olean` files for Lean (or Lake itself) are in non-standard locations.

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
  leanVersion := "<current-lean-version-string>"
}
```

We can use the command `lake build-bin` to build the package (and its dependencies, if it has them) into a native executable. The result will be placed in to `build/bin`.

```
$ lake build-bin
...
$ ./build/bin/Hello
Hello, world!
```
