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
  let token := stx[0]
  let lbrak := stx[1][0]
  let rules := stx[1][1].getArgs
  let rbrak := stx[1][2]
  let loc   := expandOptLocation stx[2]
  -- show initial state up to (incl.) `[`
  withTacticInfoContext (mkNullNode #[token, lbrak]) (pure ())
  let numRules := (rules.size + 1) / 2
  for i in [:numRules] do
    let rule := rules[i * 2]
    let sep  := rules.getD (i * 2 + 1) Syntax.missing
    -- show rule state up to (incl.) next `,`
    withTacticInfoContext (mkNullNode #[rule, sep]) do
      -- show errors on rule
      withRef rule do
        let symm := !rule[0].isNone
        let term := rule[1]
        match loc with
        | Location.targets hyps type =>
          hyps.forM (rewriteLocalDecl term symm · mode)
          if type then
            rewriteTarget term symm mode
        | Location.wildcard => rewriteAll term symm mode

@[builtinTactic Lean.Parser.Tactic.rewriteSeq] def evalRewriteSeq : Tactic :=
  evalRewriteCore TransparencyMode.instances

@[builtinTactic Lean.Parser.Tactic.erewriteSeq] def evalERewriteSeq : Tactic :=
  evalRewriteCore TransparencyMode.default

end Lean.Elab.Tactic
