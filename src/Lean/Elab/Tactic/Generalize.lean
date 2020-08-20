/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Meta.Tactic.Generalize
import Lean.Meta.Check
import Lean.Meta.Tactic.Intro
import Lean.Elab.Tactic.ElabTerm

namespace Lean
namespace Elab
namespace Tactic

private def getAuxHypothesisName (stx : Syntax) : Option Name :=
if (stx.getArg 1).isNone then none
else some ((stx.getArg 1).getIdAt 0)

private def getVarName (stx : Syntax) : Name :=
stx.getIdAt 4

private def evalGeneralizeFinalize (mvarId : MVarId) (e : Expr) (target : Expr) : MetaM (List MVarId) := do
tag         ← Meta.getMVarTag mvarId;
eType       ← Meta.inferType e;
u           ← Meta.getLevel eType;
mvar' ← Meta.mkFreshExprSyntheticOpaqueMVar target tag;
let rfl    := mkApp2 (Lean.mkConst `Eq.refl [u]) eType e;
let val    := mkApp2 mvar' e rfl;
Meta.assignExprMVar mvarId val;
let mvarId' := mvar'.mvarId!;
(_, mvarId') ← Meta.introN mvarId' 2 [] false;
pure [mvarId']

private def evalGeneralizeWithEq (h : Name) (e : Expr) (x : Name) : TacticM Unit :=
liftMetaTactic $ fun mvarId => do
  mvarId      ← Meta.generalize mvarId e x;
  mvarDecl    ← Meta.getMVarDecl mvarId;
  match mvarDecl.type with
  | Expr.forallE _ _ b _ => do
    (_, mvarId) ← Meta.intro1 mvarId false;
    eType       ← Meta.inferType e;
    u           ← Meta.getLevel eType;
    let eq     := mkApp3 (Lean.mkConst `Eq [u]) eType e (mkBVar 0);
    let target := Lean.mkForall x BinderInfo.default eType $ Lean.mkForall h BinderInfo.default eq (b.liftLooseBVars 0 1);
    evalGeneralizeFinalize mvarId e target
  | _ => Meta.throwError "unexpected type after generalize"

-- If generalizing fails, fall back to not replacing anything
private def evalGeneralizeFallback (h : Name) (e : Expr) (x : Name) : TacticM Unit :=
liftMetaTactic $ fun mvarId => do
  eType       ← Meta.inferType e;
  u           ← Meta.getLevel eType;
  mvarType    ← Meta.getMVarType mvarId;
  let eq     := mkApp3 (Lean.mkConst `Eq [u]) eType e (mkBVar 0);
  let target := Lean.mkForall x BinderInfo.default eType $ Lean.mkForall h BinderInfo.default eq mvarType;
  evalGeneralizeFinalize mvarId e target

def evalGeneralizeAux (h? : Option Name) (e : Expr) (x : Name) : TacticM Unit :=
match h? with
| none   => liftMetaTactic $ fun mvarId => do
  mvarId ← Meta.generalize mvarId e x;
  (_, mvarId) ← Meta.intro1 mvarId false;
  pure [mvarId]
| some h =>
  evalGeneralizeWithEq h e x <|> evalGeneralizeFallback h e x

@[builtinTactic «generalize»] def evalGeneralize : Tactic :=
fun stx => do
  let h? := getAuxHypothesisName stx;
  let x  := getVarName stx;
  e ← elabTerm (stx.getArg 2) none;
  evalGeneralizeAux h? e x

end Tactic
end Elab
end Lean
