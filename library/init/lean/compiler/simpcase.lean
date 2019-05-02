/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import init.lean.compiler.ir

namespace Lean
namespace IR

private def maxOccs (alts : Array Alt) : Alt :=
let (alt, _) :=
  alts.iterateFrom (alts.get 0, 1) 1 $ λ i a p,
    let aBody := a.body in
    let noccs := alts.iterateFrom 1 (i.val + 1) $ λ _ a' n,
      if a'.body == aBody then n+1 else n in
    if noccs > p.2 then (a, noccs) else p in
alt

private def addDefault (alts : Array Alt) : Array Alt :=
if alts.size <= 1 || alts.any Alt.isDefault then alts
else
  let max  := maxOccs alts in
  let alts := alts.filter $ (λ alt, alt.body == max.body) in
  alts.push (Alt.default max.body)

private def mkCase (tid : Name) (x : VarId) (alts : Array Alt) : FnBody :=
let alts := alts.filter (λ alt, alt.body != FnBody.unreachable) in
let alts := addDefault alts in
if alts.size == 0 then
  FnBody.unreachable
else if alts.size == 1 then
  (alts.get 0).body
else
  FnBody.case tid x alts

partial def FnBody.simpCase : FnBody → FnBody
| b :=
  let (bs, term) := b.flatten in
  let bs         := modifyJPVals bs FnBody.simpCase in
  match term with
  | FnBody.case tid x alts := reshape bs (mkCase tid x alts)
  | other := reshape bs term

/-- Simplify `case`
  - Remove unreachable branches.
  - Remove `case` if there is only one branch.
  - Merge most common branches using `Alt.default`. -/
@[export lean.ir.decl_simp_case_core]
def Decl.simpCase : Decl → Decl
| (Decl.fdecl f xs t b) := Decl.fdecl f xs t b.simpCase
| other                 := other

end IR
end Lean
