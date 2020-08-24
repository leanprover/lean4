/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Apply
import Lean.Meta.Tactic.Assert
import Lean.Elab.Tactic.Basic
import Lean.Elab.SyntheticMVars

namespace Lean
namespace Elab
namespace Tactic

/- `elabTerm` for Tactics and basic tactics that use it. -/

def elabTerm (stx : Syntax) (expectedType? : Option Expr) (mayPostpone := false) : TacticM Expr :=
withRef stx $ liftTermElabM $ adaptReader (fun (ctx : Term.Context) => { ctx with errToSorry := false }) $ do
  e ← Term.elabTerm stx expectedType?;
  Term.synthesizeSyntheticMVars mayPostpone;
  instantiateMVars e

@[builtinTactic «exact»] def evalExact : Tactic :=
fun stx => match_syntax stx with
  | `(tactic| exact $e) => do
    (g, gs) ← getMainGoal;
    withMVarContext g $ do {
      decl ← getMVarDecl g;
      val  ← elabTerm e decl.type;
      val  ← ensureHasType decl.type val;
      ensureHasNoMVars val;
      assignExprMVar g val
    };
    setGoals gs
  | _ => throwUnsupportedSyntax

@[builtinTactic «refine»] def evalRefine : Tactic :=
fun stx => match_syntax stx with
  | `(tactic| refine $e) => do
    (g, gs) ← getMainGoal;
    gs' ← withMVarContext g $ do {
      decl ← getMVarDecl g;
      val  ← elabTerm e decl.type;
      val  ← ensureHasType decl.type val;
      assignExprMVar g val;
      gs'  ← collectMVars val;
      tagUntaggedGoals decl.userName `refine gs';
      pure gs'
    };
    setGoals (gs' ++ gs)
  | _ => throwUnsupportedSyntax

@[builtinTactic «apply»] def evalApply : Tactic :=
fun stx => match_syntax stx with
  | `(tactic| apply $e) => do
    (g, gs) ← getMainGoal;
    gs' ← withMVarContext g $ do {
      decl ← getMVarDecl g;
      val  ← elabTerm e none true;
      gs'  ← liftMetaM $ Meta.apply g val;
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
(mvarId, others) ← getMainGoal;
withMVarContext mvarId $ do
  e ← elabTerm stx none;
  match e with
  | Expr.fvar fvarId _ => pure fvarId
  | _ => do
    type ← inferType e;
    let intro (userName : Name) (useUnusedNames : Bool) : TacticM FVarId := do {
      (fvarId, mvarId) ← liftMetaM $ do {
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
