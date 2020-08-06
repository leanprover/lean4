/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Subst
import Lean.Meta.Tactic.Clear

namespace Lean
namespace Meta

structure CaseValueSubgoal :=
(mvarId : MVarId)
(newH   : FVarId)
(subst  : FVarSubst := {})

instance CaseValueSubgoal.inhabited : Inhabited CaseValueSubgoal :=
⟨{ mvarId := arbitrary _, newH := arbitrary _ }⟩

/--
  Split goal `... |- C x` into two subgoals
  `..., (h : x = value)  |- C value`
  `..., (h : x != value) |- C x`
  The type of `x` must have decidable equality. -/
def caseValueAux (mvarId : MVarId) (fvarId : FVarId) (value : Expr) (hName : Name := `h) (subst : FVarSubst := {})
    : MetaM (CaseValueSubgoal × CaseValueSubgoal) :=
withMVarContext mvarId $ do
  tag ← getMVarTag mvarId;
  checkNotAssigned mvarId `caseValue;
  target ← getMVarType mvarId;
  xEqValue ← mkEq (mkFVar fvarId) value;
  let xNeqValue := mkApp (mkConst `Not) xEqValue;
  let thenTarget := Lean.mkForall hName BinderInfo.default xEqValue  target;
  let elseTarget := Lean.mkForall hName BinderInfo.default xNeqValue target;
  thenMVar ← mkFreshExprSyntheticOpaqueMVar thenTarget tag;
  elseMVar ← mkFreshExprSyntheticOpaqueMVar elseTarget tag;
  val ← mkAppOptM `dite #[none, xEqValue, none, thenMVar, elseMVar];
  assignExprMVar mvarId val;
  (elseH, elseMVarId) ← intro1 elseMVar.mvarId! false;
  let elseSubgoal := { mvarId := elseMVarId, newH := elseH, subst := subst : CaseValueSubgoal };
  (thenH, thenMVarId) ← intro1 thenMVar.mvarId! false;
  let symm := false;
  let clearH := false;
  (thenSubst, thenMVarId) ← substCore thenMVarId thenH symm subst clearH;
  let thenSubgoal := { mvarId := thenMVarId, newH := (thenSubst.get thenH).fvarId!, subst := thenSubst : CaseValueSubgoal };
  pure (thenSubgoal, elseSubgoal)

def caseValue (mvarId : MVarId) (fvarId : FVarId) (value : Expr) : MetaM (CaseValueSubgoal × CaseValueSubgoal) := do
s ← caseValueAux mvarId fvarId value;
appendTagSuffix s.1.mvarId `thenBranch;
appendTagSuffix s.2.mvarId `elseBranch;
pure s

structure CaseValuesSubgoal :=
(mvarId : MVarId)
(newHs  : Array FVarId := #[])
(subst  : FVarSubst := {})

instance CaseValueSubgoals.inhabited : Inhabited CaseValuesSubgoal :=
⟨{ mvarId := arbitrary _ }⟩

private def caseValuesAux (hNamePrefix : Name) (fvarId : FVarId) : Nat → MVarId → List Expr → Array FVarId → Array CaseValuesSubgoal → MetaM (Array CaseValuesSubgoal)
| i, mvarId, [],    hs, subgoals => throwTacticEx `caseValues mvarId "list of values must not be empty"
| i, mvarId, v::vs, hs, subgoals => do
  (thenSubgoal, elseSubgoal) ← caseValueAux mvarId fvarId v (hNamePrefix.appendIndexAfter i) {};
  appendTagSuffix thenSubgoal.mvarId ((`case).appendIndexAfter i);
  thenMVarId ← hs.foldlM
    (fun thenMVarId h => match thenSubgoal.subst.get h with
      | Expr.fvar fvarId _ => tryClear thenMVarId fvarId
      | _                  => pure thenMVarId)
    thenSubgoal.mvarId;
  let subgoals := subgoals.push { mvarId := thenMVarId, newHs := #[thenSubgoal.newH], subst := thenSubgoal.subst };
  match vs with
  | [] => do
    appendTagSuffix elseSubgoal.mvarId ((`case).appendIndexAfter (i+1));
    pure $ subgoals.push { mvarId := elseSubgoal.mvarId, newHs := hs.push elseSubgoal.newH, subst := {} }
  | _  => caseValuesAux (i+1) elseSubgoal.mvarId vs (hs.push elseSubgoal.newH) subgoals

/--
  Split goal `... |- C x` into values.size + 1 subgoals
  1) `..., (h_1 : x = value[0])  |- C value[0]`
  ...
  n) `..., (h_n : x = value[n - 1])  |- C value[n - 1]`
  n+1) `..., (h_1 : x != value[0]) ... (h_n : x != value[n-1]) |- C x`
  where `n = values.size`
  The type of `x` must have decidable equality. -/
def caseValues (mvarId : MVarId) (fvarId : FVarId) (values : Array Expr) (hNamePrefix := `h) : MetaM (Array CaseValuesSubgoal) :=
caseValuesAux hNamePrefix fvarId 1 mvarId values.toList #[] #[]

end Meta
end Lean
