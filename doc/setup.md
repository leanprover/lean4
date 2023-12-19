# Supported Platforms

### Tier 1

Platforms built & tested by our CI, available as nightly releases via elan (see below)

* x86-64 Linux with glibc 2.27+
* x86-64 macOS 10.15+
* x86-64 Windows 10+

### Tier 2

Platforms cross-compiled but not tested by our CI, available as nightly releases

Releases may be silently broken due to the lack of automated testing.
Issue reports and fixes are welcome.

* aarch64 Linux with glibc 2.27+
* aarch64 (Apple Silicon) macOS
* x86 (32-bit) Linux
* Emscripten Web Assembly

<!--
### Tier 3

Platforms that are known to work from manual testing, but do not come with CI or official releases
-->

# Setting Up Lean

See also the [quickstart](./quickstart.md) instructions for a standard setup with VS Code as the editor.

Release builds for all supported platforms are available at <https://github.com/leanprover/lean4/releases>.
Instead of downloading these and setting up the paths manually, however, it is recommended to use the Lean version manager [`elan`](https://github.com/leanprover/elan) instead:
```sh
$ elan self update  # in case you haven't updated elan in a while
# download & activate latest Lean 4 stable release (https://github.com/leanprover/lean4/releases)
$ elan default leanprover/lean4:stable
```

## `lake`

Lean 4 comes with a package manager named `lake`.
Use `lake init foo` to initialize a Lean package `foo` in the current directory, and `lake build` to typecheck and build it as well as all its dependencies. Use `lake help` to learn about further commands.
The general directory structure of a package `foo` is
```sh
lakefile.lean  # package configuration
lean-toolchain # specifies the lean version to use
Foo.lean       # main file, import via `import Foo`
Foo/
  A.lean       # further files, import via e.g. `import Foo.A`
  A/...        # further nesting
.lake/         # `lake` build output directory
```

After running `lake build` you will see a binary named `./.lake/build/bin/foo` and when you run it you should see the output:
```
Hello, world!
```

## Editing

Lean implements the [Language Server Protocol](https://microsoft.github.io/language-server-protocol/) that can be used for interactive development in [Emacs](https://github.com/leanprover/lean4-mode), [VS Code](https://github.com/leanprover-community/vscode-lean4), and possibly other editors.

Changes must be saved to be visible in other files, which must then be invalidated using an editor command (see links above).
