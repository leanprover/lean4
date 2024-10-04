/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Compiler.IR.Basic
import Lean.Compiler.IR.Format

namespace Lean.IR

def ensureHasDefault (alts : Array Alt) : Array Alt :=
  if alts.any Alt.isDefault then alts
  else if alts.size < 2 then alts
  else
    let last := alts.back;
    let alts := alts.pop;
    alts.push (Alt.default last.body)

private def getOccsOf (alts : Array Alt) (i : Nat) : Nat := Id.run do
  let aBody := (alts.get! i).body
  let mut n := 1
  for h : j in [i+1:alts.size] do
    if alts[j].body == aBody then
      n := n+1
  return n

private def maxOccs (alts : Array Alt) : Alt × Nat := Id.run do
  let mut maxAlt := alts[0]!
  let mut max    := getOccsOf alts 0
  for h : i in [1:alts.size] do
    let curr := getOccsOf alts i
    if curr > max then
       maxAlt := alts[i]
       max    := curr
  return (maxAlt, max)

private def addDefault (alts : Array Alt) : Array Alt :=
  if alts.size <= 1 || alts.any Alt.isDefault then alts
  else
    let (max, noccs) := maxOccs alts
    if noccs == 1 then alts
    else
      let alts := alts.filter fun alt => alt.body != max.body
      alts.push (Alt.default max.body)

private def filterUnreachable (alts : Array Alt) : Array Alt :=
  alts.filter fun alt => alt.body != FnBody.unreachable

private def mkSimpCase (tid : Name) (x : VarId) (xType : IRType) (alts : Array Alt) : FnBody :=
  let alts := filterUnreachable alts
  let alts := addDefault alts;
  if alts.size == 0 then
    FnBody.unreachable
  else if alts.size == 1 then
    (alts.get! 0).body
  else
    FnBody.case tid x xType alts

partial def FnBody.simpCase (b : FnBody) : FnBody :=
  let (bs, term) := b.flatten;
  let bs         := modifyJPs bs simpCase;
  match term with
  | FnBody.case tid x xType alts =>
    let alts := alts.map fun alt => alt.modifyBody simpCase;
    reshape bs (mkSimpCase tid x xType alts)
  | _     => reshape bs term

/-- Simplify `case`
  - Remove unreachable branches.
  - Remove `case` if there is only one branch.
  - Merge most common branches using `Alt.default`. -/
def Decl.simpCase (d : Decl) : Decl :=
  match d with
  | .fdecl (body := b) .. => d.updateBody! b.simpCase
  | other => other

end Lean.IR
