/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Rewrite
import Lean.Meta.Tactic.Replace
import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.ElabTerm
import Lean.Elab.Tactic.Location

namespace Lean
namespace Elab
namespace Tactic

open Meta

@[builtinMacro Lean.Parser.Tactic.rewriteSeq] def expandRewriteTactic : Macro :=
fun stx =>
  let seq := ((stx.getArg 1).getArg 1).getArgs.getSepElems;
  let loc := stx.getArg 2;
  pure $ mkNullNode $ seq.map fun rwRule => Syntax.node `Lean.Parser.Tactic.rewrite #[mkAtomFrom rwRule "rewrite ", rwRule, loc]

def rewriteTarget (stx : Syntax) (symm : Bool) : TacticM Unit := do
(g, gs) ← getMainGoal;
withMVarContext g do
  e ← elabTerm stx none true;
  gDecl ← getMVarDecl g;
  target ← instantiateMVars gDecl.type;
  r ← liftMetaM $ rewrite g target e symm;
  g' ← liftMetaM $ replaceTargetEq g r.eNew r.eqProof;
  setGoals (g' :: r.mvarIds ++ gs)

def rewriteLocalDeclFVarId (stx : Syntax) (symm : Bool) (fvarId : FVarId) : TacticM Unit := do
(g, gs) ← getMainGoal;
withMVarContext g do
  e ← elabTerm stx none true;
  localDecl ← getLocalDecl fvarId;
  rwResult ← liftMetaM $ rewrite g localDecl.type e symm;
  replaceResult ← liftMetaM $ replaceLocalDecl g fvarId rwResult.eNew rwResult.eqProof;
  setGoals (replaceResult.mvarId :: rwResult.mvarIds ++ gs)

def rewriteLocalDecl (stx : Syntax) (symm : Bool) (userName : Name) : TacticM Unit := do
withMainMVarContext do
  localDecl ← getLocalDeclFromUserName userName;
  rewriteLocalDeclFVarId stx symm localDecl.fvarId

def rewriteAll (stx : Syntax) (symm : Bool) : TacticM Unit := do
worked ← try $ rewriteTarget stx symm;
withMainMVarContext do
  lctx ← getLCtx;
  worked ← lctx.getFVarIds.foldrM -- We must traverse backwards because `replaceLocalDecl` uses the revert/intro idiom
    (fun fvarId worked => do
      worked' ← try $ rewriteLocalDeclFVarId stx symm fvarId;
      pure $ worked || worked')
    worked;
  unless worked do
    (mvarId, _) ← getMainGoal;
    liftMetaM $ throwTacticEx `rewrite mvarId ("did not find instance of the pattern in the current goal")

/-
```
def rwRule    := parser! optional (unicodeSymbol "←" "<-") >> termParser
def «rewrite» := parser! "rewrite" >> rwRule >> optional location
```
-/
@[builtinTactic Lean.Parser.Tactic.rewrite] def evalRewrite : Tactic :=
fun stx => do
  let rule := stx.getArg 1;
  let symm := !(rule.getArg 0).isNone;
  let term := rule.getArg 1;
  let loc  := expandOptLocation $ stx.getArg 2;
  match loc with
  | Location.target => rewriteTarget term symm
  | Location.localDecls userNames => userNames.forM (rewriteLocalDecl term symm)
  | Location.wildcard => rewriteAll term symm

end Tactic
end Elab
end Lean
