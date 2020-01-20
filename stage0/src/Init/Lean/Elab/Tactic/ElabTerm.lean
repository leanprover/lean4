/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Meta.Tactic.Apply
import Init.Lean.Elab.Tactic.Basic
import Init.Lean.Elab.SynthesizeSyntheticMVars

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

end Tactic
end Elab
end Lean
