/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.IR.Basic
import Lean.Compiler.IR.FreeVars

namespace Lean.IR

partial def reshapeWithoutDead (bs : Array FnBody) (term : FnBody) : FnBody :=
  let rec reshape (bs : Array FnBody) (b : FnBody) (used : IndexSet) :=
    if bs.isEmpty then b
    else
      let curr := bs.back
      let bs   := bs.pop
      let keep (_ : Unit) :=
        let used := curr.collectFreeIndices used
        let b    := curr.setBody b
        reshape bs b used
      let keepIfUsed (vidx : Index) :=
        if used.contains vidx then keep ()
        else reshape bs b used
      match curr with
      | FnBody.vdecl x _ _ _  => keepIfUsed x.idx
      -- TODO: we should keep all struct/union projections because they are used to ensure struct/union values are fully consumed.
      | FnBody.jdecl j _ _ _  => keepIfUsed j.idx
      | _                     => keep ()
  reshape bs term term.freeIndices

partial def FnBody.elimDead (b : FnBody) : FnBody :=
  let (bs, term) := b.flatten
  let bs         := modifyJPs bs elimDead
  let term       := match term with
    | FnBody.case tid x xType alts =>
      let alts := alts.map fun alt => alt.modifyBody elimDead
      FnBody.case tid x xType alts
    | other => other
  reshapeWithoutDead bs term

/-- Eliminate dead let-declarations and join points -/
def Decl.elimDead (d : Decl) : Decl :=
  match d with
  | .fdecl (body := b) .. => d.updateBody! b.elimDead
  | other => other

end Lean.IR
