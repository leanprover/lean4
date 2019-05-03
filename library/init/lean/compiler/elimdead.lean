/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.compiler.ir

namespace Lean
namespace IR

partial def reshapeWithoutDeadAux : Array FnBody → FnBody → IndexSet → FnBody
| bs b used :=
  if bs.isEmpty then b
  else
    let curr := bs.back in
    let bs   := bs.pop in
    let keep (_ : Unit) :=
      let used := curr.collectFreeVars used in
      let b    := curr <;> b in
      reshapeWithoutDeadAux bs b used in
    let keepIfUsed (vidx : Index) :=
      if used.contains vidx then keep ()
      else reshapeWithoutDeadAux bs b used in
    match curr with
    | FnBody.vdecl x _ _  _  := keepIfUsed x.idx
    | FnBody.jdecl j _ _ _ _ := keepIfUsed j.idx
    | _                      := keep ()

def reshapeWithoutDead (bs : Array FnBody) (term : FnBody) : FnBody :=
reshapeWithoutDeadAux bs term term.freeVars

partial def FnBody.elimDead : FnBody → FnBody
| b :=
  let (bs, term) := b.flatten in
  let bs         := modifyJPs bs FnBody.elimDead in
  let term       := match term with
    | FnBody.case tid x alts :=
      let alts := alts.hmap $ λ alt, alt.modifyBody FnBody.elimDead in
      FnBody.case tid x alts
    | other := other in
  reshapeWithoutDead bs term

/-- Eliminate dead let-declarations and join points -/
def Decl.elimDead : Decl → Decl
| (Decl.fdecl f xs t b) := Decl.fdecl f xs t b.elimDead
| other                 := other

end IR
end Lean
