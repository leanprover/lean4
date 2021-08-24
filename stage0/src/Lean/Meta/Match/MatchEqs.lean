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

/--
  Helper method. Recall that alternatives that do not have variables have a `Unit` parameter to ensure
  they are not eagerly evaluated. -/
private def toFVarsRHSArgs (ys : Array Expr) : MetaM (Array Expr × Array Expr) := do
  if ys.size == 1 && (← inferType ys[0]).isConstOf ``Unit then
    return (#[], #[mkConst ``Unit.unit])
  else
    return (ys, ys)

/--
  Simplify/filter hypotheses that ensure that a match alternative does not match the previous ones.
  Remark: if there is no overlaping between the alternatives, the empty array is returned. -/
private partial def simpHs (hs : Array Expr) (numPatterns : Nat) : MetaM (Array Expr) := do
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
where
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


/--
  Helper method for `proveCondEqThm`. Given a goal of the form `C.rec ... xMajor = rhs`,
  apply `cases xMajor`. -/
private def casesOnStuckLHS (mvarId : MVarId) : MetaM (Array MVarId) := do
  let target ← getMVarType mvarId
  if let some (_, lhs, rhs) ← matchEq? target then
    matchConstRec lhs.getAppFn (fun _ => failed) fun recVal _ => do
      let args := lhs.getAppArgs
      if recVal.getMajorIdx >= args.size then failed
      let mut major := args[recVal.getMajorIdx]
      unless major.isFVar do failed
      return (← cases mvarId major.fvarId!).map fun s => s.mvarId
  else
    failed
where
  failed {α} : MetaM α := throwError "'casesOnStuckLHS' failed"

/--
  Helper method for proving a conditional equational theorem associated with an alternative of
  the `match`-eliminator `matchDeclName`. `type` contains the type of the theorem. -/
partial def proveCondEqThm (matchDeclName : Name) (type : Expr) : MetaM Expr := do
  let type ← instantiateMVars type
  withLCtx {} {} <| forallTelescope type fun ys target => do
    let mvar0  ← mkFreshExprSyntheticOpaqueMVar target
    let mvarId ← deltaTarget mvar0.mvarId! (. == matchDeclName)
    trace[Meta.Match.matchEqs] "{MessageData.ofGoal mvarId}"
    go mvarId 0
    mkLambdaFVars ys (← instantiateMVars mvar0)
where
  go (mvarId : MVarId) (depth : Nat) : MetaM Unit := withIncRecDepth do
    let mvarId' ← modifyTargetEqLHS mvarId whnfCore
    let mvarId := mvarId'
    trace[Meta.debug] "proveLoop [{depth}]\n{MessageData.ofGoal mvarId}"
    let subgoals ←
      (do applyRefl mvarId; return #[])
      <|>
      (do contradiction mvarId { genDiseq := true }; return #[])
      <|>
      (casesOnStuckLHS mvarId)
      <|>
      (do let mvarId' ← simpIfTarget mvarId (useDecide := true)
          if mvarId' == mvarId then throwError "simpIf failed"
          return #[mvarId'])
      <|>
      (do if let some (s₁, s₂) ← splitIfTarget? mvarId then
            let mvarId₁ ← trySubst s₁.mvarId s₁.fvarId
            return #[mvarId₁, s₂.mvarId]
          else
            throwError "spliIf failed")
      <|>
      (throwError "failed to generate equality theorems for `match` expression, support for array literals has not been implemented yet{MessageData.ofGoal mvarId}")
    subgoals.forM (go . (depth+1))


/-- Construct new local declarations `xs` with types `altTypes`, and then execute `f xs`  -/
private partial def withElimAlts (altTypes : Array Expr) (f : Array Expr → MetaM α) : MetaM α := do
  let rec go (i : Nat) (xs : Array Expr) : MetaM α := do
    if h : i < altTypes.size then
      let hName := (`h).appendIndexAfter (i+1)
      withLocalDeclD hName (altTypes.get ⟨i, h⟩) fun x =>
        go (i+1) (xs.push x)
    else
      f xs
  go 0 #[]

/--
  Create conditional equations and elimination principle for the given
  match auxiliary declaration. -/
partial def mkEquationsFor (matchDeclName : Name) :  MetaM Unit := do
  let constInfo ← getConstInfo matchDeclName
  let us := constInfo.levelParams.map mkLevelParam
  let some matchInfo ← getMatcherInfo? matchDeclName | throwError "'{matchDeclName}' is not a matcher function"
  forallTelescopeReducing constInfo.type fun xs matchResultType => do
    let params := xs[:matchInfo.numParams]
    let motive := xs[matchInfo.getMotivePos]
    let alts   := xs[xs.size - matchInfo.numAlts:]
    let firstDiscrIdx := matchInfo.numParams + 1
    let discrs := xs[firstDiscrIdx : firstDiscrIdx + matchInfo.numDiscrs]
    let mut notAlts := #[]
    let mut idx := 1
    let mut elimAltTypes := #[]
    for alt in alts do
      let altType ← inferType alt
      trace[Meta.debug] ">> {altType}"
      let (notAlt, elimAltType) ← forallTelescopeReducing altType fun ys altResultType => do
        let (ys, rhsArgs) ← toFVarsRHSArgs ys
        let patterns := altResultType.getAppArgs
        let mut hs := #[]
        for notAlt in notAlts do
          hs := hs.push (← instantiateForall notAlt patterns)
        hs ← simpHs hs patterns.size
        trace[Meta.Match.matchEqs] "hs: {hs}"
        let elimAltType ← mkForallFVars ys (← hs.foldrM (init := altResultType) mkArrow)
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
        let thmVal ← proveCondEqThm matchDeclName thmType
        trace[Meta.debug] "thmVal: {thmVal}"
        let thmName := matchDeclName ++ ((`eq).appendIndexAfter idx)
        addDecl <| Declaration.thmDecl {
          name        := thmName
          levelParams := constInfo.levelParams
          type        := thmType
          value       := thmVal
        }
        return (notAlt, elimAltType)
      notAlts := notAlts.push notAlt
      elimAltTypes := elimAltTypes.push elimAltType
      trace[Meta.Match.matchEqs] "elimAltType: {elimAltType}"
      idx := idx + 1
    -- Define eliminator with conditional/refined alternatives
    withElimAlts elimAltTypes fun altsNew => do
      let elimType ← mkForallFVars (params.toArray ++ #[motive] ++ discrs.toArray ++ altsNew) matchResultType
      trace[Meta.Match.matchEqs] "elimType: {elimType}"
      -- TODO: construct value of type `elimType`
      return ()

builtin_initialize registerTraceClass `Meta.Match.matchEqs

end Lean.Meta.Match
