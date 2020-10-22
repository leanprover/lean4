#lang lean4
/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Attributes

namespace Lean

inductive ReducibilityStatus
| reducible | semireducible | irreducible

instance : Inhabited ReducibilityStatus := ⟨ReducibilityStatus.semireducible⟩

builtin_initialize reducibilityAttrs : EnumAttributes ReducibilityStatus ←
  registerEnumAttributes `reducibility
    [(`reducible, "reducible", ReducibilityStatus.reducible),
     (`semireducible, "semireducible", ReducibilityStatus.semireducible),
     (`irreducible, "irreducible", ReducibilityStatus.irreducible)]

@[export lean_get_reducibility_status]
def getReducibilityStatus (env : Environment) (n : Name) : ReducibilityStatus :=
match reducibilityAttrs.getValue env n with
| some s => s
| none   => ReducibilityStatus.semireducible

@[export lean_set_reducibility_status]
def setReducibilityStatus (env : Environment) (n : Name) (s : ReducibilityStatus) : Environment :=
match reducibilityAttrs.setValue env n s with
| Except.ok env => env
| _ => env -- TODO(Leo): we should extend EnumAttributes.setValue in the future and ensure it never fails

def isReducible (env : Environment) (n : Name) : Bool :=
match getReducibilityStatus env n with
| ReducibilityStatus.reducible => true
| _ => false

end Lean
