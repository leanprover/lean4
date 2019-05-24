/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.compiler.ir.basic
import init.lean.compiler.ir.freevars

namespace Lean
namespace IR

partial def pushProjs : Array FnBody → Array Alt → Array IndexSet → Array FnBody → IndexSet → Array FnBody × Array Alt
| bs alts altsF ctx ctxF :=
  if bs.isEmpty then (ctx.reverse, alts)
  else
    let b    := bs.back in
    let bs   := bs.pop in
    let done (_ : Unit) := (bs.push b ++ ctx.reverse, alts) in
    let skip (_ : Unit) := pushProjs bs alts altsF (ctx.push b) (b.collectFreeIndices ctxF) in
    let push (x : VarId) (t : IRType) (v : Expr) :=
        if !ctxF.contains x.idx then
          let alts := alts.hmapIdx $ λ i alt, alt.modifyBody $ λ b',
             if (altsF.get i).contains x.idx then b <;> b'
             else b' in
          let altsF  := altsF.hmap $ λ s, if s.contains x.idx then b.collectFreeIndices s else s in
          pushProjs bs alts altsF ctx ctxF
        else
          skip () in
    match b with
    | FnBody.vdecl x t v _ :=
      match v with
      | Expr.proj _ _      := push x t v
      | Expr.uproj _ _     := push x t v
      | Expr.sproj _ _ _   := push x t v
      | Expr.isShared _    := skip ()
      | Expr.isTaggedPtr _ := skip ()
      | _                  := done ()
    | _ := done ()

partial def FnBody.pushProj : FnBody → FnBody
| b :=
  let (bs, term) := b.flatten in
  let bs         := modifyJPs bs FnBody.pushProj in
  match term with
  | FnBody.case tid x alts :=
    let altsF      := alts.map $ λ alt, alt.body.freeIndices in
    let (bs, alts) := pushProjs bs alts altsF Array.empty {x.idx} in
    let alts       := alts.hmap $ λ alt, alt.modifyBody FnBody.pushProj in
    let term       := FnBody.case tid x alts in
    reshape bs term
  | other := reshape bs term

/-- Push projections inside `case` branches. -/
def Decl.pushProj : Decl → Decl
| (Decl.fdecl f xs t b) := Decl.fdecl f xs t b.pushProj
| other                 := other

end IR
end Lean
