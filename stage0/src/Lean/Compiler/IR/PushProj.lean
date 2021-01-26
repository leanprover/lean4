/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.IR.Basic
import Lean.Compiler.IR.FreeVars
import Lean.Compiler.IR.NormIds

namespace Lean.IR

partial def pushProjs (bs : Array FnBody) (alts : Array Alt) (altsF : Array IndexSet) (ctx : Array FnBody) (ctxF : IndexSet) : Array FnBody × Array Alt :=
  if bs.isEmpty then (ctx.reverse, alts)
  else
    let b    := bs.back
    let bs   := bs.pop
    let done (_ : Unit) := (bs.push b ++ ctx.reverse, alts)
    let skip (_ : Unit) := pushProjs bs alts altsF (ctx.push b) (b.collectFreeIndices ctxF)
    let push (x : VarId) (t : IRType) (v : Expr) :=
        if !ctxF.contains x.idx then
          let alts := alts.mapIdx $ fun i alt => alt.modifyBody $ fun b' =>
             if (altsF.get! i).contains x.idx then b.setBody b'
             else b'
          let altsF  := altsF.map $ fun s => if s.contains x.idx then b.collectFreeIndices s else s
          pushProjs bs alts altsF ctx ctxF
        else
          skip ()
    match b with
    | FnBody.vdecl x t v _ =>
      match v with
      | Expr.proj _ _      => push x t v
      | Expr.uproj _ _     => push x t v
      | Expr.sproj _ _ _   => push x t v
      | Expr.isShared _    => skip ()
      | Expr.isTaggedPtr _ => skip ()
      | _                  => done ()
    | _ => done ()

partial def FnBody.pushProj (b : FnBody) : FnBody :=
  let (bs, term) := b.flatten
  let bs         := modifyJPs bs pushProj
  match term with
  | FnBody.case tid x xType alts =>
    let altsF      := alts.map $ fun alt => alt.body.freeIndices
    let (bs, alts) := pushProjs bs alts altsF #[] (mkIndexSet x.idx)
    let alts       := alts.map $ fun alt => alt.modifyBody pushProj
    let term       := FnBody.case tid x xType alts
    reshape bs term
  | other => reshape bs term

/-- Push projections inside `case` branches. -/
def Decl.pushProj (d : Decl) : Decl :=
  match d with
  | Decl.fdecl (body := b) .. => d.updateBody! b.pushProj |>.normalizeIds
  | other => other

end Lean.IR
