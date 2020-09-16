/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.CollectMVars
import Lean.Meta.Tactic.Apply
import Lean.Meta.Tactic.Assert
import Lean.Elab.Tactic.Basic
import Lean.Elab.SyntheticMVars

namespace Lean
namespace Elab
namespace Tactic

open Meta

/- `elabTerm` for Tactics and basic tactics that use it. -/

def elabTerm (stx : Syntax) (expectedType? : Option Expr) (mayPostpone := false) : TacticM Expr :=
withRef stx $ liftTermElabM $ adaptReader (fun (ctx : Term.Context) => { ctx with errToSorry := false }) $ do
  e ← Term.elabTerm stx expectedType?;
  Term.synthesizeSyntheticMVars mayPostpone;
  instantiateMVars e

def elabTermEnsuringType (stx : Syntax) (expectedType? : Option Expr) (mayPostpone := false) : TacticM Expr := do
e ← elabTerm stx expectedType? mayPostpone;
ensureHasType expectedType? e

@[builtinTactic «exact»] def evalExact : Tactic :=
fun stx => match_syntax stx with
  | `(tactic| exact $e) => do
    (g, gs) ← getMainGoal;
    withMVarContext g $ do {
      decl ← getMVarDecl g;
      val  ← elabTermEnsuringType e decl.type;
      ensureHasNoMVars val;
      assignExprMVar g val
    };
    setGoals gs
  | _ => throwUnsupportedSyntax

@[builtinMacro Lean.Parser.Tactic.admit] def expandAdmit : Macro :=
fun _ => `(tactic| exact sorry)

/- If `allowNaturalHoles == true`, then we allow the resultant expression to contain unassigned "natural" metavariables.
   Recall that "natutal" metavariables are created for explicit holes `_` and implicit arguments. They are meant to be
   filled by typing constraints.
   "Synthetic" metavariables are meant to be filled by tactics and are usually created using the synthetic hole notation `?<hole-name>`. -/
def refineCore (mvarId : MVarId) (stx : Syntax) (tagSuffix : Name) (allowNaturalHoles : Bool := false) : TacticM (List MVarId) :=
withMVarContext mvarId do
  decl ← getMVarDecl mvarId;
  val  ← elabTermEnsuringType stx decl.type;
  assignExprMVar mvarId val;
  newMVarIds ← getMVarsNoDelayed val;
  newMVarIds ←
    if allowNaturalHoles then
      pure newMVarIds.toList
    else do {
      naturalMVarIds ← newMVarIds.filterM fun mvarId => do { mvarDecl ← getMVarDecl mvarId; pure mvarDecl.kind.isNatural };
      syntheticMVarIds ← newMVarIds.filterM fun mvarId => do { mvarDecl ← getMVarDecl mvarId; pure $ !mvarDecl.kind.isNatural };
      liftM $ Term.logUnassignedUsingErrorContext naturalMVarIds;
      pure syntheticMVarIds.toList
    };
  tagUntaggedGoals decl.userName tagSuffix newMVarIds;
  pure newMVarIds

@[builtinTactic «refine»] def evalRefine : Tactic :=
fun stx => match_syntax stx with
  | `(tactic| refine $e) => do
    (g, gs) ← getMainGoal;
    /- Remark: only synthetic holes become new goals (we are using `allowNaturalHoles == false`). -/
    gs' ← refineCore g e `refine;
    setGoals (gs' ++ gs)
  | _ => throwUnsupportedSyntax

@[builtinTactic «refine!»] def evalRefineBang : Tactic :=
fun stx => match_syntax stx with
  | `(tactic| refine! $e) => do
    (g, gs) ← getMainGoal;
    /- Remark all unassigned metavariables become new goals. We consider delayed assignments as assignments here. -/
    gs' ← refineCore g e `refine true;
    setGoals (gs' ++ gs)
  | _ => throwUnsupportedSyntax

@[builtinTactic Lean.Parser.Tactic.apply] def evalApply : Tactic :=
fun stx => match_syntax stx with
  | `(tactic| apply $e) => do
    (g, gs) ← getMainGoal;
    gs' ← withMVarContext g $ do {
      decl ← getMVarDecl g;
      val  ← elabTerm e none true;
      gs'  ← liftMetaM $ Meta.apply g val;
      liftTermElabM $ Term.synthesizeSyntheticMVarsNoPostponing;
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
