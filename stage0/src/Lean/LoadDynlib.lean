/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/

namespace Lean

/--
Dynamically loads a shared library so that its symbols can be used by
the Lean interpreter (e.g., for interpreting `@[extern]` declarations).
Equivalent to passing `--load-dynlib=lib` to `lean`.

Note that Lean never unloads libraries.
-/
@[extern "lean_load_dynlib"]
opaque loadDynlib (path : @& System.FilePath) : IO Unit
