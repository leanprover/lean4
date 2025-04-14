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

private opaque Dynlib.SymbolImpl (dynlib : Dynlib) : NonemptyType.{0}
/-- A reference to a symbol within a dynamic library. -/
def Dynlib.Symbol (dynlib : Dynlib) := SymbolImpl dynlib |>.type
instance : Nonempty (Dynlib.Symbol dynlib) := Dynlib.SymbolImpl dynlib |>.property

/--
Dynamically loads a shared library.

The path may also be used perform a system-dependent search for library.
To avoid this, use an absolute path (e.g., from `IO.FS.realPath`).
-/
@[extern "lean_dynlib_load"]
opaque Dynlib.load (path : @& System.FilePath) : IO Dynlib

/-- Returns the symbol of the dynamic library with the specified name (if any).  -/
@[extern "lean_dynlib_get"]
opaque Dynlib.get? (dynlib : @& Dynlib) (sym : @& String) : Option dynlib.Symbol

/--
Runs a module initializer function.
The symbol should have the signature `(builtin : Bool) → IO Unit`
(e.g., `initialize_Foo(uint8_t builtin, obj_arg)`).

This function is unsafe because there is no guarantee the symbol has the
expected signature. An invalid symbol can thus produce undefined behavior.
Furthermore, if the initializer introduces pointers (e.g., function closures)
from the dynamic library into the global state, future garbage collection of
the library will produce undefined behavior. In such cases, garbage collection
of the dynamic library can be prevented via `Runtime.markPersistent` or
`Runtime.forget`.
-/
@[extern "lean_dynlib_symbol_run_as_init"]
unsafe opaque Dynlib.Symbol.runAsInit {dynlib : @& Dynlib} (sym : @& dynlib.Symbol) : IO Unit

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
  -- Safety: There are no concurrent accesses to `dynlib` at this point.
  let _ ← unsafe Runtime.markPersistent dynlib

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
  -- Lean libraries can be prefixed with `lib` or suffixed with `_shared`
  -- under some configurations. We strip these from the initializer symbol.
  let name := name.stripPrefix "lib" |>.stripSuffix "_shared"
  let name := s!"initialize_{name}"
  let some sym := dynlib.get? name
    | throw <| IO.userError s!"error loading plugin, initializer not found '{name}'"
  -- Lean never unloads plugins (once initialized).
  -- Safety: There are no concurrent accesses to `dynlib` at this point.
  let _ ← unsafe Runtime.markPersistent dynlib
  /-
  Safety:
  * As `dynlib` is marked persistent, there is no danger of garbage collection.
  * There is still no guarantee that `sym` has the proper signature, but this
    is about as safe as it can be. The initializer naming convention helps
    avoid accidentally mistaking non-plugins as plugins.
  -/
  unsafe sym.runAsInit
