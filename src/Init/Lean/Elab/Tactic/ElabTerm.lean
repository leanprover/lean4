/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Elab.Tactic.Basic
import Init.Lean.Elab.SynthesizeSyntheticMVars

namespace Lean
namespace Elab
namespace Tactic

/- `elabTerm` for Tactics and basic tactics that use it. -/

def elabTerm (stx : Syntax) (expectedType? : Option Expr) : TacticM Expr :=
liftTermElabM $ adaptReader (fun (ctx : Term.Context) => { errToSorry := false, .. ctx }) $ do
  e ← Term.elabTerm stx expectedType?;
  Term.synthesizeSyntheticMVars false;
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
      collectMVars ref val
    };
    setGoals (gs' ++ gs)
  | _ => throwUnsupportedSyntax

end Tactic
end Elab
end Lean
