/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Init.System.IO

namespace Lean

private opaque DynlibImpl : NonemptyType.{0}
/-- A dynamic library handle. -/
def Dynlib := DynlibImpl.type
instance : Nonempty Dynlib := DynlibImpl.property

/--
Dynamically loads a shared library.

The path may also be used perform a system-dependent search for library.
To avoid this, use an absolute path (e.g., from `IO.FS.realPath`).
-/
@[extern "lean_dynlib_load"]
opaque Dynlib.load (path : @& System.FilePath) : IO Dynlib

/--
Dynamically loads a shared library so that its symbols can be used by
the Lean interpreter (e.g., for interpreting `@[extern]` declarations).
Equivalent to passing `--load-dynlib=path` to `lean`.

**Lean never unloads libraries.** Attempting to load a library that defines
symbols shared with a previously loaded library (including itself) will error.
If multiple libraries share common symbols, those symbols should be linked
and loaded as separate libraries.
-/
@[export lean_load_dynlib]
def loadDynlib (path : @& System.FilePath) : IO Unit := do
  let dynlib ← Dynlib.load path
  -- Lean never unloads libraries.
  let _ ← unsafe Runtime.markPersistent dynlib

/--
Runs a module initializer function.
The function symbol should have the signature `(builtin : Bool) → IO Unit`
(e.g., `initialize_Foo(uint8_t builtin, obj_arg)`).

This function is marked `unsafe` because there is no way to guarantee
the symbol has the expected signature. An invalid symbol can thus produce
undefined behavior.
-/
@[extern "lean_dynlib_run_init"]
unsafe opaque Dynlib.runInit (dynlib : @& Dynlib) (sym : @& String) : IO Unit

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
@[export lean_load_plugin]
def loadPlugin (path : System.FilePath) : IO Unit := do
  -- We never want to look up plugins using the system library search
  let path ← IO.FS.realPath path
  let some name := path.fileStem
    | throw <| IO.userError s!"error, plugin has invalid file name '{path}'"
  let dynlib ← Dynlib.load path
  -- Lean never unloads plugins.
  -- This also ensures that any data from the library mixed
  -- into the global state by the initializer is not freed early.
  let dynlib ← unsafe Runtime.markPersistent dynlib
  -- Lean libraries can be prefixed with `lib` or suffixed with `_shared`
  -- under some configurations. We strip these from the initializer symbol.
  let sym := name.stripPrefix "lib" |>.stripSuffix "_shared"
  let sym := s!"initialize_{sym}"
  unsafe dynlib.runInit sym
