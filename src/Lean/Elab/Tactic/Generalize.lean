/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Meta.Tactic.Generalize
import Lean.Meta.Check
import Lean.Meta.Tactic.Intro
import Lean.Elab.Tactic.ElabTerm

namespace Lean.Elab.Tactic
open Meta

private def getAuxHypothesisName (stx : Syntax) : Option Name :=
  if stx[1].isNone then none
  else some stx[1][0].getId

private def getVarName (stx : Syntax) : Name :=
  stx[4].getId

private def evalGeneralizeFinalize (mvarId : MVarId) (e : Expr) (target : Expr) : MetaM (List MVarId) := do
  let tag    ← Meta.getMVarTag mvarId
  let eType  ← inferType e
  let u      ← Meta.getLevel eType
  let mvar'  ← Meta.mkFreshExprSyntheticOpaqueMVar target tag
  let rfl    := mkApp2 (Lean.mkConst `Eq.refl [u]) eType e
  let val    := mkApp2 mvar' e rfl
  assignExprMVar mvarId val
  let mvarId' := mvar'.mvarId!
  let (_, mvarId') ← Meta.introNP mvarId' 2
  pure [mvarId']

private def evalGeneralizeWithEq (h : Name) (e : Expr) (x : Name) : TacticM Unit :=
  liftMetaTactic fun mvarId => do
    let mvarId      ← Meta.generalize mvarId e x false
    let mvarDecl    ← getMVarDecl mvarId
    match mvarDecl.type with
    | Expr.forallE _ _ b _ =>
      let (_, mvarId) ← Meta.intro1P mvarId
      let eType       ← inferType e
      let u           ← Meta.getLevel eType
      let eq          := mkApp3 (Lean.mkConst `Eq [u]) eType e (mkBVar 0)
      let target      := Lean.mkForall x BinderInfo.default eType $ Lean.mkForall h BinderInfo.default eq (b.liftLooseBVars 0 1)
      evalGeneralizeFinalize mvarId e target
    | _ => throwError "unexpected type after generalize"

-- If generalizing fails, fall back to not replacing anything
private def evalGeneralizeFallback (h : Name) (e : Expr) (x : Name) : TacticM Unit :=
  liftMetaTactic fun mvarId => do
    let eType    ← inferType e
    let u        ← Meta.getLevel eType
    let mvarType ← Meta.getMVarType mvarId
    let eq       := mkApp3 (Lean.mkConst `Eq [u]) eType e (mkBVar 0)
    let target   := Lean.mkForall x BinderInfo.default eType $ Lean.mkForall h BinderInfo.default eq mvarType
    evalGeneralizeFinalize mvarId e target

def evalGeneralizeAux (h? : Option Name) (e : Expr) (x : Name) : TacticM Unit :=
  match h? with
  | none   => liftMetaTactic fun mvarId => do
    let mvarId ← Meta.generalize mvarId e x false
    let (_, mvarId) ← Meta.intro1P mvarId
    pure [mvarId]
  | some h =>
    evalGeneralizeWithEq h e x <|> evalGeneralizeFallback h e x

@[builtinTactic Lean.Parser.Tactic.generalize] def evalGeneralize : Tactic := fun stx =>
  withMainContext do
    let h? := getAuxHypothesisName stx
    let x  := getVarName stx
    let e ← elabTerm stx[2] none
    evalGeneralizeAux h? e x

end Lean.Elab.Tactic
