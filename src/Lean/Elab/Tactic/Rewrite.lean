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
namespace Lean.Elab.Tactic
open Meta

private def expand (kind : SyntaxNodeKind) (token : String) (stx : Syntax) : Syntax := do
  let rwRules := stx[1][1].getSepArgs
  let loc     := stx[2]
  let mut newTacs := #[]
  for i in [:rwRules.size] do
    let rwRule := rwRules[i]
    -- We use `stx` as "position provider" for the first rule
    -- Without this change, we don't get correct information when we hover over `rw`/`rewrite`/`erewrite` with multiple rewrites
    let ref ← if i == 0 then stx else pure rwRule
    newTacs := newTacs.push <| Syntax.node kind #[mkAtomFrom ref token, rwRule, loc]
  return mkNullNode newTacs

@[builtinMacro Lean.Parser.Tactic.rewriteSeq] def expandRewriteTactic : Macro := fun stx =>
  return expand ``Parser.Tactic.rewrite  "rewrite " stx

@[builtinMacro Lean.Parser.Tactic.erewriteSeq] def expandERewriteTactic : Macro := fun stx =>
  return expand ``Parser.Tactic.erewrite  "erewrite " stx

def rewriteTarget (stx : Syntax) (symm : Bool) (mode : TransparencyMode) : TacticM Unit := do
  Term.withSynthesize <| withMainContext do
    let e ← elabTerm stx none true
    let r ← rewrite (← getMainGoal) (← getMainTarget) e symm (mode := mode)
    let mvarId' ← replaceTargetEq (← getMainGoal) r.eNew r.eqProof
    replaceMainGoal (mvarId' :: r.mvarIds)

def rewriteLocalDeclFVarId (stx : Syntax) (symm : Bool) (fvarId : FVarId) (mode : TransparencyMode) : TacticM Unit := do
  Term.withSynthesize <| withMainContext do
    let e ← elabTerm stx none true
    let localDecl ← getLocalDecl fvarId
    let rwResult ← rewrite (← getMainGoal) localDecl.type e symm (mode := mode)
    let replaceResult ← replaceLocalDecl (← getMainGoal) fvarId rwResult.eNew rwResult.eqProof
    replaceMainGoal (replaceResult.mvarId :: rwResult.mvarIds)

def rewriteLocalDecl (stx : Syntax) (symm : Bool) (userName : Name) (mode : TransparencyMode) : TacticM Unit :=
  withMainContext do
    let localDecl ← getLocalDeclFromUserName userName
    rewriteLocalDeclFVarId stx symm localDecl.fvarId mode

def rewriteAll (stx : Syntax) (symm : Bool) (mode : TransparencyMode) : TacticM Unit := do
  let worked ← tryTactic <| rewriteTarget stx symm mode
  withMainContext do
    let mut worked := worked
    -- We must traverse backwards because `replaceLocalDecl` uses the revert/intro idiom
    for fvarId in (← getLCtx).getFVarIds.reverse do
      worked := worked || (← tryTactic <| rewriteLocalDeclFVarId stx symm fvarId mode)
    unless worked do
      let mvarId ← getMainGoal
      throwTacticEx `rewrite mvarId "did not find instance of the pattern in the current goal"

def evalRewriteCore (mode : TransparencyMode) : Tactic := fun stx => do
  let rule := stx[1]
  let symm := !rule[0].isNone
  let term := rule[1]
  let loc  := expandOptLocation stx[2]
  match loc with
  | Location.targets hyps type =>
     hyps.forM (rewriteLocalDecl term symm · mode)
     if type then
      rewriteTarget term symm mode
  | Location.wildcard => rewriteAll term symm mode

/-
```
def rwRule    := leading_parser optional (unicodeSymbol "←" "<-") >> termParser
def «rewrite» := leading_parser "rewrite" >> rwRule >> optional location
```
-/
@[builtinTactic Lean.Parser.Tactic.rewrite] def evalRewrite : Tactic :=
  evalRewriteCore TransparencyMode.instances

@[builtinTactic Lean.Parser.Tactic.erewrite] def evalERewrite : Tactic :=
  evalRewriteCore TransparencyMode.default

end Lean.Elab.Tactic
