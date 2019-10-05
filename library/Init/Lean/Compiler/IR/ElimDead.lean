/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Compiler.IR.Basic
import Init.Lean.Compiler.IR.FreeVars

namespace Lean
namespace IR

partial def reshapeWithoutDeadAux : Array FnBody → FnBody → IndexSet → FnBody
| bs, b, used =>
  if bs.isEmpty then b
  else
    let curr := bs.back;
    let bs   := bs.pop;
    let keep (_ : Unit) :=
      let used := curr.collectFreeIndices used;
      let b    := curr.setBody b;
      reshapeWithoutDeadAux bs b used;
    let keepIfUsed (vidx : Index) :=
      if used.contains vidx then keep ()
      else reshapeWithoutDeadAux bs b used;
    match curr with
    | FnBody.vdecl x _ _ _  => keepIfUsed x.idx
    | FnBody.jdecl j _ _ _  => keepIfUsed j.idx
    | _                     => keep ()

def reshapeWithoutDead (bs : Array FnBody) (term : FnBody) : FnBody :=
reshapeWithoutDeadAux bs term term.freeIndices

partial def FnBody.elimDead : FnBody → FnBody
| b =>
  let (bs, term) := b.flatten;
  let bs         := modifyJPs bs FnBody.elimDead;
  let term       := match term with
    | FnBody.case tid x xType alts =>
      let alts := alts.map $ fun alt => alt.modifyBody FnBody.elimDead;
      FnBody.case tid x xType alts
    | other => other;
  reshapeWithoutDead bs term

/-- Eliminate dead let-declarations and join points -/
def Decl.elimDead : Decl → Decl
| Decl.fdecl f xs t b => Decl.fdecl f xs t b.elimDead
| other               => other

end IR
end Lean
