/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Lean.Elab.Command
public import Lean.Meta.VirtualStructure

public section

namespace Lean.Elab.Command

/--
`newtype N := ty with proj` declares a type `N` definitionally equal to `ty`, together with a
constructor `N.mk : ty → N` and a projector `N.proj : N → ty`, and marks all three
`@[irreducible]`:
```
@[irreducible] def N := ty
@[irreducible] def N.mk (a : ty) : N := a
@[irreducible] def N.proj (n : N) : ty := n
```
This is the "irreducible type alias" pattern used to avoid defeq abuse while keeping a
zero-overhead representation identical to `ty` (e.g. to cast `List ty` to `List N`). Unlike a
hand-written version of this pattern, `newtype` also registers `N.mk`/`N.proj` as a virtual
constructor/projector pair, so that `N.proj (N.mk a)` reduces to `a` (see
`Lean.Meta.reduceVirtualProj?`) even though both stay irreducible otherwise.
-/
syntax (name := newtypeCmd) "newtype " ident " := " term " with " ident : command

@[builtin_command_elab newtypeCmd]
def elabNewtype : CommandElab
  | `(newtype $id:ident := $ty:term with $projId:ident) => do
    let ctorId := mkIdentFrom id (id.getId ++ `mk) (canonical := true)
    let typeProjId := mkIdentFrom id (id.getId ++ projId.getId) (canonical := true)
    elabCommand <| ← `(def $id := $ty)
    elabCommand <| ← `(def $ctorId (a : $ty) : $id := a)
    elabCommand <| ← `(def $typeProjId (n : $id) : $ty := n)
    elabCommand <| ← `(attribute [irreducible] $id $ctorId $typeProjId)
    let ns ← getCurrNamespace
    let info : VirtualStructureInfo := {
      typeName := ns ++ id.getId
      ctorName := ns ++ ctorId.getId
      projName := ns ++ typeProjId.getId
    }
    modifyEnv (registerVirtualStructure · info)
  | _ => throwUnsupportedSyntax

end Lean.Elab.Command
