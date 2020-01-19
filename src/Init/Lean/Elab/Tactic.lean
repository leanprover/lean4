/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Init.Lean.Elab.Term
import Init.Lean.Elab.Tactic.Basic

namespace Lean
namespace Elab

namespace Term

def mkTacticMVar (ref : Syntax) (type : Expr) (tacticCode : Syntax) : TermElabM Expr := do
mvar ← mkFreshExprMVar ref type MetavarKind.syntheticOpaque `main;
let mvarId := mvar.mvarId!;
registerSyntheticMVar ref mvarId $ SyntheticMVarKind.tactic tacticCode;
pure mvar

@[builtinTermElab tacticBlock] def elabTacticBlock : TermElab :=
fun stx expectedType? =>
  match expectedType? with
  | some expectedType => mkTacticMVar stx expectedType (stx.getArg 1)
  | none => throwError stx ("invalid tactic block, expected type has not been provided")

open Tactic (TacticM evalTactic getUnsolvedGoals)

def liftTacticElabM {α} (ref : Syntax) (mvarId : MVarId) (x : TacticM α) : TermElabM α :=
withMVarContext mvarId $ fun ctx s =>
  match x { ref := ref, main := mvarId, .. ctx } { goals := [mvarId], .. s } with
  | EStateM.Result.error ex newS => EStateM.Result.error (Term.Exception.ex ex) newS.toTermState
  | EStateM.Result.ok a newS     => EStateM.Result.ok a newS.toTermState

def reportUnsolvedGoals (ref : Syntax) (goals : List MVarId) : TermElabM Unit :=
throwError ref $ "unsolved goals" ++ Format.line ++ MessageData.joinSep (goals.map $ MessageData.ofGoal) Format.line

def ensureAssignmentHasNoMVars (ref : Syntax) (mvarId : MVarId) : TermElabM Unit := do
val ← instantiateMVars ref (mkMVar mvarId);
when val.hasMVar $ throwError ref ("tactic failed, result still contain metavariables" ++ indentExpr val)

def runTactic (ref : Syntax) (mvarId : MVarId) (tacticCode : Syntax) : TermElabM Unit := do
modify $ fun s => { mctx := s.mctx.instantiateMVarDeclMVars mvarId, .. s };
remainingGoals ← liftTacticElabM ref mvarId $ do { evalTactic tacticCode; getUnsolvedGoals };
let tailRef := ref.getTailWithInfo.getD ref;
unless remainingGoals.isEmpty (reportUnsolvedGoals tailRef remainingGoals);
ensureAssignmentHasNoMVars tailRef mvarId

end Term

end Elab
end Lean
