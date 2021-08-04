/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
namespace Lean

private builtin_initialize importingRef : IO.Ref Bool ← IO.mkRef false

/- We say Lean is "initializing" when it is executing `builtin_initialize` declarations and importing modules.
   Recall that Lean excutes `initialize` declarations while importing modules. -/
def initializing : IO Bool :=
  IO.initializing <||> importingRef.get

/--
  Excute `x` with "importing" flag turned on.
  When the "importing" flag is set to true, we allow user-extensions defined with with
  the `initialize` command to update global references.

  IMPORTANT: There is no semaphore controlling the access to these global references.
  We assume these global references are updated by a single execution thread.
  This is true in the Lean frontend where we process the `import` commands at the beginning
  of the execution only. Users must make sure that `importModules` is used, there is only
  one execution thread accessing the global references.
-/
def withImporting (x : IO α) : IO α :=
  try
    importingRef.set true
    x
  finally
    importingRef.set false

end Lean
