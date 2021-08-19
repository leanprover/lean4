/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Match.Match
import Lean.Meta.Tactic.Apply
import Lean.Meta.Tactic.Delta
import Lean.Meta.Tactic.SplitIf

namespace Lean.Meta.Match

private def isMatchValue (e : Expr) : Bool :=
  e.isNatLit || e.isCharLit || e.isStringLit

partial def mkEquationsFor (matchDeclName : Name) :  MetaM Unit := do
  let constInfo ← getConstInfo matchDeclName
  let us := constInfo.levelParams.map mkLevelParam
  let some matchInfo ← getMatcherInfo? matchDeclName | throwError "'{matchDeclName}' is not a matcher function"
  forallTelescopeReducing constInfo.type fun xs _ => do
    let params := xs[:matchInfo.numParams]
    let motive := xs[matchInfo.getMotivePos]
    let alts   := xs[xs.size - matchInfo.numAlts:]
    let firstDiscrIdx := matchInfo.numParams + 1
    let discrs := xs[firstDiscrIdx : firstDiscrIdx + matchInfo.numDiscrs]
    let mut notAlts := #[]
    for alt in alts do
      let altType ← inferType alt
      trace[Meta.debug] ">> {altType}"
      notAlts ← forallTelescopeReducing altType fun ys altResultType => do
        let (ys, rhsArgs) ← toFVarsRHSArgs ys
        let patterns := altResultType.getAppArgs
        let mut hs := #[]
        for notAlt in notAlts do
          hs := hs.push (← instantiateForall notAlt patterns)
        hs ← simpHs hs patterns.size
        trace[Meta.debug] "hs: {hs}"
        -- Create a proposition for representing terms that do not match `patterns`
        let mut notAlt := mkConst ``False
        for discr in discrs.toArray.reverse, pattern in patterns.reverse do
          notAlt ← mkArrow (← mkEq discr pattern) notAlt
        notAlt ← mkForallFVars (discrs ++ ys) notAlt
        trace[Meta.debug] "notAlt: {notAlt}"
        let lhs := mkAppN (mkConst constInfo.name us) (params ++ #[motive] ++ patterns ++ alts)
        let rhs := mkAppN alt rhsArgs
        let thmType ← mkEq lhs rhs
        let thmType ← hs.foldrM (init := thmType) mkArrow
        let thmType ← mkForallFVars (params ++ #[motive] ++ alts ++ ys) thmType
        let thmVal ← prove thmType
        trace[Meta.debug] "thmVal: {thmVal}"
        -- check thmVal -- TODO remove
        return notAlts.push notAlt
where
  toFVarsRHSArgs (ys : Array Expr) : MetaM (Array Expr × Array Expr) := do
    if ys.size == 1 && (← inferType ys[0]).isConstOf ``Unit then
      return (#[], #[mkConst ``Unit.unit])
    else
      return (ys, ys)

  simpEq (lhs : Expr) (rhs : Expr) : OptionT (StateRefT (Array Expr) MetaM) Unit := do
    if isMatchValue lhs && isMatchValue rhs then
      unless (← isDefEq lhs rhs) do
        failure
    else if rhs.isFVar then
      -- Ignore case since it matches anything
      pure ()
    else match lhs.arrayLit?, rhs.arrayLit? with
      | some (_, lhsArgs), some (_, rhsArgs) =>
        if lhsArgs.length != rhsArgs.length then
          failure
        else
          for lhsArg in lhsArgs, rhsArg in rhsArgs do
            simpEq lhsArg rhsArg
      | _, _ =>
        match toCtorIfLit lhs |>.constructorApp? (← getEnv), toCtorIfLit rhs |>.constructorApp? (← getEnv) with
        | some (lhsCtor, lhsArgs), some (rhsCtor, rhsArgs) =>
          if lhsCtor.name == rhsCtor.name then
            for lhsArg in lhsArgs[lhsCtor.numParams:], rhsArg in rhsArgs[lhsCtor.numParams:] do
              simpEq lhsArg rhsArg
          else
            failure
        | _, _ =>
          let newEq ← mkEq lhs rhs
          modify fun eqs => eqs.push newEq

  simpEqs (eqs : Array Expr) : OptionT (StateRefT (Array Expr) MetaM) Unit := do
    eqs.forM fun eq =>
      match eq.eq? with
      | some (_, lhs, rhs) => simpEq lhs rhs
      | _ => throwError "failed to generate equality theorems for 'match', equality expected{indentExpr eq}"

  simpHs (hs : Array Expr) (numPatterns : Nat) : MetaM (Array Expr) :=
    hs.filterMapM fun h => forallTelescope h fun ys _ => do
      trace[Meta.debug] "ys: {ys}"
      let xs  := ys[:ys.size - numPatterns].toArray
      let eqs ← ys[ys.size - numPatterns : ys.size].toArray.mapM inferType
      if let some eqsNew ← simpEqs eqs *> get |>.run |>.run' #[] then
        let newH ← eqsNew.foldrM (init := mkConst ``False) mkArrow
        let xs ← xs.filterM fun x => dependsOn newH x.fvarId!
        return some (← mkForallFVars xs newH)
      else
        none

  failed : MetaM Unit := throwError "" -- TODO

  proveLoop (mvarId : MVarId) (depth : Nat) : MetaM Unit := withIncRecDepth do
    let mvarId ← modifyTargetEqLHS mvarId whnfCore
    trace[Meta.debug] "proveLoop\n{MessageData.ofGoal mvarId}"
    (applyRefl mvarId)
    <|>
    (contradiction mvarId)
    <|>
    (do let mvarId' ← simpIfTarget mvarId (useDecide := true)
        trace[Meta.debug] "simpIfTarget\n{MessageData.ofGoal mvarId'}"
        if mvarId' == mvarId then failed
        proveLoop mvarId' (depth+1))
    <|>
    (do if let some (s₁, s₂) ← splitIfTarget? mvarId then
          proveLoop s₁.mvarId (depth+1)
          proveLoop s₂.mvarId (depth+1)
        else
          failed)
    <|>
    (do trace[Meta.debug] "TODO\n{← ppGoal mvarId}"
        -- TODO
        admit mvarId)

  prove (type : Expr) : MetaM Expr :=
    withLCtx {} {} <| forallTelescope type fun ys target => do
      let mvar0  ← mkFreshExprSyntheticOpaqueMVar target
      let mvarId ← deltaTarget mvar0.mvarId! (. == matchDeclName)
      proveLoop mvarId 0
      mkLambdaFVars ys (← instantiateMVars mvar0)

end Lean.Meta.Match
