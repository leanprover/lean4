/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.compiler.ir.basic
import init.lean.compiler.ir.format

namespace Lean
namespace IR

def ensureHasDefault (alts : Array Alt) : Array Alt :=
if alts.any Alt.isDefault then alts
else if alts.size < 2 then alts
else
  let last := alts.back;
  let alts := alts.pop;
  alts.push (Alt.default last.body)

private def getOccsOf (alts : Array Alt) (i : Nat) : Nat :=
let aBody := (alts.get i).body;
alts.iterateFrom 1 (i + 1) $ fun _ a' n =>
  if a'.body == aBody then n+1 else n

private def maxOccs (alts : Array Alt) : Alt × Nat :=
alts.iterateFrom (alts.get 0, getOccsOf alts 0) 1 $ fun i a p =>
  let noccs := getOccsOf alts i.val;
  if noccs > p.2 then (alts.fget i, noccs) else p

private def addDefault (alts : Array Alt) : Array Alt :=
if alts.size <= 1 || alts.any Alt.isDefault then alts
else
  let (max, noccs) := maxOccs alts;
  if noccs == 1 then alts
  else
    let alts := alts.filter $ (fun alt => alt.body != max.body);
    alts.push (Alt.default max.body)

private def mkSimpCase (tid : Name) (x : VarId) (xType : IRType) (alts : Array Alt) : FnBody :=
let alts := alts.filter (fun alt => alt.body != FnBody.unreachable);
let alts := addDefault alts;
if alts.size == 0 then
  FnBody.unreachable
else if alts.size == 1 then
  (alts.get 0).body
else
  FnBody.case tid x xType alts

partial def FnBody.simpCase : FnBody → FnBody
| b =>
  let (bs, term) := b.flatten;
  let bs         := modifyJPs bs FnBody.simpCase;
  match term with
  | FnBody.case tid x xType alts =>
    let alts := alts.map $ fun alt => alt.modifyBody FnBody.simpCase;
    reshape bs (mkSimpCase tid x xType alts)
  | other => reshape bs term

/-- Simplify `case`
  - Remove unreachable branches.
  - Remove `case` if there is only one branch.
  - Merge most common branches using `Alt.default`. -/
def Decl.simpCase : Decl → Decl
| Decl.fdecl f xs t b => Decl.fdecl f xs t b.simpCase
| other               => other

end IR
end Lean
