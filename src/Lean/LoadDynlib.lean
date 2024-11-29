/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Init.System.IO

namespace Lean

/--
Dynamically loads a shared library so that its symbols can be used by
the Lean interpreter (e.g., for interpreting `@[extern]` declarations).
Equivalent to passing `--load-dynlib=path` to `lean`.

**Lean never unloads libraries.** Attempting to load a library that defines
symbols shared with a previously loaded library (including itself) will error.
If multiple libraries share common symbols, those symbols should be linked
and loaded as separate libraries.
-/
@[extern "lean_load_dynlib"]
opaque loadDynlib (path : @& System.FilePath) : IO Unit

/--
Loads a Lean plugin and runs its initializers.

A Lean plugin is a shared library built from a Lean module.
This means it has an `initialize_<module-name>` symbol that runs the
module's initializers (including its imports' initializers). Initializers
are declared with the `initialize` or `builtin_initialize` commands.

This is similar to passing `--plugin=path` to `lean`.
Lean environment initializers, such as definitions calling
`registerEnvExtension`, also require `Lean.initializing` to be `true`.
To enable them, use `loadPlugin` within a `withImporting` block. This will
set  `Lean.initializing` (but not `IO.initializing`).

**Lean never unloads plugins.** Attempting to load a plugin that defines
symbols shared with a previously loaded plugin (including itself) will error.
If multiple plugins share common symbols (e.g., imports), those symbols
should be linked and loaded separately.
-/
@[extern "lean_load_plugin"]
opaque loadPlugin (path : @& System.FilePath) : IO Unit
