# Lake

Lake (Lean Make) is a new build system and package manager for Lean 4.
With Lake, package configuration is written in Lean inside a dedicated `package.lean` file stored in the root of the package directory. Each `package.lean` includes a `package` definition (akin to `main`) which defines the package's configuration.

## Building and Running Lake

In order to properly build Lake, you must provide `leanpkg build bin` with some additional linker options to have it create an executable that can correctly interpret the Lake package configuration files.

On Unix:

```
$ leanpkg build bin LINK_OPTS=-rdynamic
```

On Windows (MSYS2):

```
$ leanpkg build bin LINK_OPTS=-Wl,--export-all
```

When running the built executable, you also must make sure that `LEAN_PATH` includes the build directory of Lake (for Lake's `.olean` files) and Lean's library directory for stdlib's (ex., `Init`'s) `.olean` files.

For example:

```
$ LEAN_PATH="<lean-home>/lib/lean:<lake-home>/build" lake build bin
```

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

We can use the command `lake build bin` to build the module (and its dependencies, if it has them) and a native executable. The latter of which will be written to `build/bin`.

```
$ lake build bin
...
$ ./build/bin/Hello
Hello, world!
```
