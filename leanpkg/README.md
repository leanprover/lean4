# leanpkg

`leanpkg` is the package manager for the [Lean theorem prover](https://leanprover.github.io).  It downloads dependencies and manages what modules you can import in your Lean files.

There are two important files for `leanpkg` in each package:
 * `leanpkg.toml`: a manifest describing the package name, version, and dependencies
 * `leanpkg.path`: this file is created by `leanpkg configure` and should not be added to git.  It contains the paths to the dependencies on the current machine.

Dependencies can be fetched from git repositories; in this case `leanpkg` will remember the current revision.  You need to change the revision in the `[dependencies]` section manually if you want to update the dependency.

### General guidelines

 * Run the `lean` command-line tool from a directory inside your package.
 * In vscode, open the package as a folder.

### Working on existing packages

You need to run `leanpkg configure` first, in order to download dependencies and generate the `leanpkg.path` file.
```
git clone https://github.com/leanprover/library_dev
cd library_dev
leanpkg configure
```

### Creating new packages

The `leanpkg new` command creates a new package.  You can use `leanpkg add` to add dependencies, or add them manually if you prefer:
```
leanpkg new my_awesome_pkg
cd my_awesome_pkg
leanpkg add https://github.com/leanprover/library_dev
```

You can now add new `.lean` files inside the `my_awesome_pkg` directory.

### Files that are not in packages

It is reasonably common to have thousands of "scratch" files lying around that are not part of a package.  Files that are not inside a package themselves can still use dependencies fetched via `leanpkg`.  These dependencies are stored in `~/.lean/leanpkg.toml` and can be modified with `leanpkg install`:
```
leanpkg install https://github.com/leanprover/smt2_interface
```

After this, you can use the `smt2_interface` package in all files that do not belong to a package themselves.

## Format of `leanpkg.toml`

```toml
[package]
name = "my_awesome_pkg"
version = "0.1"

[dependencies]
demopkg = { path = "relative/path/to/demopkg" }
library_dev = { git = "https://github.com/leanprover/library_dev",
  rev = "62f7883d937861b618ae8bd645ee16ec137dd0bd" }
```

By default source files are assumed to be directly in the root directory of the package.  You can optionally add a `path = "src"` attribute to the `[package]` section that selects a different directory.

## Import resolution

Lean supports two kinds of imports:
```lean
import theory.set_theory   -- absolute
import .basic              -- relative
```

Relative imports are always relative to the current file name.

Absolute imports are resolved according to the entries in the `leanpkg.path` file.  That is, when executing `import theory.set_theory`, Lean looks for a file called `theory/set_theory.lean` in all (transitive) dependencies as well as the current package.