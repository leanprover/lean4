/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Meta.Tactic.Apply
import Init.Lean.Meta.Tactic.Assert
import Init.Lean.Elab.Tactic.Basic
import Init.Lean.Elab.SyntheticMVars

namespace Lean
namespace Elab
namespace Tactic

/- `elabTerm` for Tactics and basic tactics that use it. -/

def elabTerm (stx : Syntax) (expectedType? : Option Expr) (mayPostpone := false) : TacticM Expr :=
liftTermElabM $ adaptReader (fun (ctx : Term.Context) => { errToSorry := false, .. ctx }) $ do
  e ← Term.elabTerm stx expectedType?;
  Term.synthesizeSyntheticMVars mayPostpone;
  Term.instantiateMVars stx e

@[builtinTactic «exact»] def evalExact : Tactic :=
fun stx => match_syntax stx with
  | `(tactic| exact $e) => do
    let ref := stx;
    (g, gs) ← getMainGoal stx;
    withMVarContext g $ do {
      decl ← getMVarDecl g;
      val  ← elabTerm e decl.type;
      val  ← ensureHasType ref decl.type val;
      ensureHasNoMVars ref val;
      assignExprMVar g val
    };
    setGoals gs
  | _ => throwUnsupportedSyntax

@[builtinTactic «refine»] def evalRefine : Tactic :=
fun stx => match_syntax stx with
  | `(tactic| refine $e) => do
    let ref := stx;
    (g, gs) ← getMainGoal stx;
    gs' ← withMVarContext g $ do {
      decl ← getMVarDecl g;
      val  ← elabTerm e decl.type;
      val  ← ensureHasType ref decl.type val;
      assignExprMVar g val;
      gs'  ← collectMVars ref val;
      tagUntaggedGoals decl.userName `refine gs';
      pure gs'
    };
    setGoals (gs' ++ gs)
  | _ => throwUnsupportedSyntax

@[builtinTactic «apply»] def evalApply : Tactic :=
fun stx => match_syntax stx with
  | `(tactic| apply $e) => do
    let ref := stx;
    (g, gs) ← getMainGoal stx;
    gs' ← withMVarContext g $ do {
      decl ← getMVarDecl g;
      val  ← elabTerm e none true;
      gs'  ← liftMetaM ref $ Meta.apply g val;
      liftTermElabM $ Term.synthesizeSyntheticMVars false;
      pure gs'
    };
    -- TODO: handle optParam and autoParam
    setGoals (gs' ++ gs)
  | _ => throwUnsupportedSyntax

/--
  Elaborate `stx`. If it a free variable, return it. Otherwise, assert it, and return the free variable.
  Note that, the main goal is updated when `Meta.assert` is used in the second case. -/
def elabAsFVar (stx : Syntax) (userName? : Option Name := none) : TacticM FVarId := do
(mvarId, others) ← getMainGoal stx;
withMVarContext mvarId $ do
  e ← elabTerm stx none;
  match e with
  | Expr.fvar fvarId _ => pure fvarId
  | _ => do
    type ← inferType stx e;
    let intro (userName : Name) (useUnusedNames : Bool) : TacticM FVarId := do {
      (fvarId, mvarId) ← liftMetaM stx $ do {
        mvarId ← Meta.assert mvarId userName type e;
        Meta.intro1 mvarId useUnusedNames
      };
      setGoals $ mvarId::others;
      pure fvarId
    };
    match userName? with
    | none          => intro `h true
    | some userName => intro userName false

end Tactic
end Elab
end Lean
