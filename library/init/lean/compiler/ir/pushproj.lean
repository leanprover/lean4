/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.compiler.ir.basic

namespace Lean
namespace IR

partial def pushProjs : Array FnBody → Array Alt → Array IndexSet → Array FnBody → IndexSet → Array FnBody × Array Alt
| bs alts afvs ps vs :=
  if bs.isEmpty then (ps.reverse, alts)
  else
    let b    := bs.back in
    let bs   := bs.pop in
    let done (_ : Unit) := (bs.push b ++ ps.reverse, alts) in
    let skip (_ : Unit) := pushProjs bs alts afvs (ps.push b) (b.collectFreeVars vs) in
    match b with
    | FnBody.vdecl x t v _ :=
      match v with
      | Expr.proj _ _    :=
        if !vs.contains x.idx && !afvs.all (λ s, s.contains x.idx) then
          let alts := alts.hmapIdx $ λ i alt, alt.modifyBody $ λ b',
             if (afvs.get i).contains x.idx then b <;> b'
             else b' in
          let fvs  := afvs.hmap $ λ s, if s.contains x.idx then b.collectFreeVars s else s in
          pushProjs bs alts fvs ps vs
        else
          skip ()
      | Expr.uproj _ _   := skip ()
      | Expr.sproj _ _ _ := skip ()
      | _                := done ()
    | _ := done ()

partial def FnBody.pushProj : FnBody → FnBody
| b :=
  let (bs, term) := b.flatten in
  let bs         := modifyJPs bs FnBody.pushProj in
  match term with
  | FnBody.case tid x alts :=
    let afvs       := alts.map $ λ alt, alt.body.freeVars in
    let (bs, alts) := pushProjs bs alts afvs Array.empty {x.idx} in
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
