/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
namespace Lean

builtin_initialize importingRef : IO.Ref Bool ← IO.mkRef false

/- We say Lean is "initializing" when it is executing `builtin_initialize` declarations and importing modules.
   Recall that Lean excutes `initialize` declarations while importing modules. -/
def initializing : IO Bool :=
  IO.initializing <||> importingRef.get

def withImporting (x : IO α) : IO α :=
  try
    importingRef.set true
    x
  finally
    importingRef.set false

end Lean
