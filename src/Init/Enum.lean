/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.NotationExtra
import Init.Data.Range
import Init.Data.Stream

/--
  Macro for declaring big enumeration types. It is more efficient than using `inductive`.

  It also generates the instances `BEq`, `DecidableEq`, `Inhabited`, and `Repr` for the new type
-/
macro "enum " n:ident " where " cs:(group("| " ident))+ : command => open Lean in do
  let cs := cs.getArgs
  let numCtors := cs.size
  let structDecl ← `(structure $n:ident where (val : Fin $(quote numCtors)))
  let derivingCmd ← `(deriving instance BEq, DecidableEq, Inhabited for $n:ident)
  let currNamespace ← Macro.getCurrNamespace
  let mkCtorName (ctorDeclStx : Syntax) : Name :=
    n.getId ++ ctorDeclStx[1].getId
  let mut ctorDefs := #[]
  for c in cs, i in [:numCtors] do
    let ctorName := mkCtorName c
    let ctorDef ← `(@[matchPattern] abbrev $(mkIdentFrom c ctorName):ident : $n:ident := ⟨$(quote i)⟩)
    ctorDefs := ctorDefs.push ctorDef
  -- generate `Repr` instance
  let ctorFmts ← cs.mapM fun c =>
    `(Std.format $(quote <| toString (currNamespace ++ mkCtorName c)))
  let reprInst ← `(
    def enumFmts : Array Std.Format := [ $(ctorFmts),*].toArray
    instance : Repr $n := ⟨fun e _ => enumFmts[e.val.val]⟩)
  return mkNullNode (#[structDecl, derivingCmd, reprInst] ++ ctorDefs)
