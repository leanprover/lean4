/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Match.MatcherApp.Basic
import Lean.Meta.Tactic.Simp.Main
import Lean.Meta.Tactic.SplitIf
import Lean.Meta.Tactic.Apply
import Lean.Meta.Tactic.Generalize

namespace Lean.Meta
namespace Split

def getSimpMatchContext : MetaM Simp.Context := do
   Simp.mkContext
      (simpTheorems   := {})
      (congrTheorems := (← getSimpCongrTheorems))
      (config        := { Simp.neutralConfig with dsimp := false })

def simpMatch (e : Expr) : MetaM Simp.Result := do
  let discharge? ← SplitIf.mkDischarge?
  (·.1) <$> Simp.main e (← getSimpMatchContext) (methods := { pre, discharge? })
where
  pre (e : Expr) : SimpM Simp.Step := do
    unless (← isMatcherApp e) do
      return Simp.Step.continue
    let matcherDeclName := e.getAppFn.constName!
    -- First try to reduce matcher
    match (← reduceRecMatcher? e) with
    | some e' => return Simp.Step.done { expr := e' }
    | none    => Simp.simpMatchCore matcherDeclName e

def simpMatchTarget (mvarId : MVarId) : MetaM MVarId := mvarId.withContext do
  let target ← instantiateMVars (← mvarId.getType)
  let r ← simpMatch target
  applySimpResultToTarget mvarId target r

private def simpMatchCore (matchDeclName : Name) (matchEqDeclName : Name) (e : Expr) : MetaM Simp.Result := do
  let discharge? ← SplitIf.mkDischarge?
  (·.1) <$> Simp.main e (← getSimpMatchContext) (methods := { pre, discharge? })
where
  pre (e : Expr) : SimpM Simp.Step := do
    if e.isAppOf matchDeclName then
      -- First try to reduce matcher
      match (← reduceRecMatcher? e) with
      | some e' => return .done { expr := e' }
      | none    =>
      -- Try lemma
      let simpTheorem := {
        origin := .decl matchEqDeclName
        proof := mkConst matchEqDeclName
        rfl := (← isRflTheorem matchEqDeclName)
      }
      match (← withReducible <| Simp.tryTheorem? e simpTheorem) with
      | none => return .continue
      | some r => return .done r
    else
      return .continue

private def simpMatchTargetCore (mvarId : MVarId) (matchDeclName : Name) (matchEqDeclName : Name) : MetaM MVarId := do
  mvarId.withContext do
    let target ← instantiateMVars (← mvarId.getType)
    let r ← simpMatchCore matchDeclName matchEqDeclName target
    match r.proof? with
    | some proof => mvarId.replaceTargetEq r.expr proof
    | none => mvarId.replaceTargetDefEq r.expr

private partial def withEqs (lhs rhs : Array Expr) (k : Array Expr → Array Expr → MetaM α) : MetaM α := do
  go 0 #[] #[]
where
  go (i : Nat) (hs : Array Expr) (rfls : Array Expr) : MetaM α := do
    if i < lhs.size then
      withLocalDeclD (← mkFreshUserName `heq) (← mkEqHEq lhs[i]! rhs[i]!) fun h => do
        let rfl ← if (← inferType h).isEq then mkEqRefl lhs[i]! else mkHEqRefl lhs[i]!
        go (i+1) (hs.push h) (rfls.push rfl)
    else
      k hs rfls

/--
Internal exception for discriminant generalization failures due to type errors.
-/
builtin_initialize discrGenExId : InternalExceptionId ←
  registerInternalExceptionId `discrGeneralizationFailure

def isDiscrGenException (ex : Exception) : Bool :=
  match ex with
  | .internal id => id == discrGenExId
  | _ => false

/--
  This method makes sure each discriminant is a free variable.
  Return the tuple `(discrsNew, discrEqs, mvarId)`. `discrsNew` in an array representing the new discriminants, `discrEqs` is an array of auxiliary equality hypotheses
  that connect the new discriminants to the original terms they represent.
  Remark: `discrEqs.size ≤ discrsNew.size`

  Remark:
    We should only generalize `discrs` occurrences as `match`-expression discriminants.
    For example, given the following goal.
    ```
    x : Nat
    ⊢ (match g x with
        | 0 => 1
        | Nat.succ y => g x) =
        2 * x + 1
    ```
    we should not generalize the `g x` in the rhs of the second alternative, and the two resulting goals
    for the `split` tactic  should be
    ```
    case h_1
    x x✝ : Nat
    h✝ : g x = 0
    ⊢ 1 = 2 * x + 1

    case h_2
    x x✝ y✝ : Nat
    h✝ : g x = Nat.succ y✝
    ⊢ g x = 2 * x + 1
    ```
-/
private partial def generalizeMatchDiscrs (mvarId : MVarId) (matcherDeclName : Name) (motiveType : Expr) (discrs : Array Expr) : MetaM (Array FVarId × Array FVarId × MVarId) := mvarId.withContext do
  if discrs.all (·.isFVar) then
    return (discrs.map (·.fvarId!), #[], mvarId)
  let some matcherInfo ← getMatcherInfo? matcherDeclName | unreachable!
  let numDiscrEqs := matcherInfo.getNumDiscrEqs -- Number of `h : discr = pattern` equations
  let (targetNew, rfls) ←
    forallTelescope motiveType fun discrVars _ =>
    withEqs discrs discrVars fun eqs rfls => do
      let foundRef ← IO.mkRef false
      let rec mkNewTarget (e : Expr) : MetaM Expr := do
        let pre (e : Expr) : MetaM TransformStep := do
          if !e.isAppOfArity matcherDeclName matcherInfo.arity then
            return .continue
          let some matcherApp ← matchMatcherApp? e | return .continue
          for matcherDiscr in matcherApp.discrs, discr in discrs do
            unless matcherDiscr == discr do
              trace[split.debug] "discr mismatch {matcherDiscr} != {discr}"
              return .continue
          let matcherApp := { matcherApp with discrs := discrVars }
          foundRef.set true
          let mut altsNew := #[]
          for h : i in [:matcherApp.alts.size] do
            let alt := matcherApp.alts[i]
            let altNumParams := matcherApp.altNumParams[i]!
            let altNew ← lambdaTelescope alt fun xs body => do
              if xs.size < altNumParams || xs.size < numDiscrEqs then
                throwError "internal error in `split` tactic: encountered an unexpected `match` expression alternative\nthis error typically occurs when the `match` expression has been constructed using meta-programming."
              let body ← mkLambdaFVars xs[altNumParams:] (← mkNewTarget body)
              let ys  := xs[:altNumParams - numDiscrEqs]
              if numDiscrEqs == 0 then
                mkLambdaFVars ys body
              else
                let altEqs := xs[altNumParams - numDiscrEqs : altNumParams]
                withNewAltEqs matcherInfo eqs altEqs fun altEqsNew subst => do
                  let body := body.replaceFVars altEqs subst
                  mkLambdaFVars (ys++altEqsNew) body
            altsNew := altsNew.push altNew
          return .done { matcherApp with alts := altsNew }.toExpr
        transform (← instantiateMVars e) pre
      let targetNew ← mkNewTarget (← mvarId.getType)
      unless (← foundRef.get) do
        throwError "internal error in `split` tactic: failed to find match-expression discriminants\nthis error typically occurs when the `split` tactic internal functions have been used in a new meta-program"
      let targetNew ← mkForallFVars (discrVars ++ eqs) targetNew
      unless (← isTypeCorrect targetNew) do
        throw <| Exception.internal discrGenExId
      return (targetNew, rfls)
    let mvarNew ← mkFreshExprSyntheticOpaqueMVar targetNew (← mvarId.getTag)
    trace[split.debug] "targetNew:\n{mvarNew.mvarId!}"
    mvarId.assign (mkAppN (mkAppN mvarNew discrs) rfls)
    let (discrs', mvarId') ← mvarNew.mvarId!.introNP discrs.size
    let (discrEqs, mvarId') ← mvarId'.introNP discrs.size
    return (discrs', discrEqs, mvarId')
where
  /--
    - `eqs` are free variables `h_eq : discr = discrVar`. `eqs.size == discrs.size`
    - `altEqs` are free variables of the form `h_altEq : discr = pattern`. `altEqs.size = numDiscrEqs ≤ discrs.size`
    This method executes `k altEqsNew subst` where
    - `altEqsNew` are fresh free variables of the form `h_altEqNew : discrVar = pattern`
    - `subst` are terms of the form `h_eq.trans h_altEqNew : discr = pattern`. We use `subst` later to replace occurrences of `h_altEq` with `h_eq.trans h_altEqNew`.
   -/
  withNewAltEqs (matcherInfo : MatcherInfo) (eqs : Array Expr) (altEqs : Array Expr) (k : Array Expr → Array Expr → MetaM Expr) : MetaM Expr := do
    let eqs' := (eqs.zip matcherInfo.discrInfos).filterMap fun (eq, info) => if info.hName?.isNone then none else some eq
    -- `eqs'.size == altEqs.size ≤ eqs.size`
    let rec go (i : Nat) (altEqsNew : Array Expr) (subst : Array Expr) : MetaM Expr := do
      if i < altEqs.size then
        let altEqDecl ← getFVarLocalDecl altEqs[i]!
        let eq := eqs'[i]!
        let eqType ← inferType eq
        let altEqType := altEqDecl.type
        match eqType.eq?, altEqType.eq? with
        | some (_, _, discrVar), some (_, _ /- discr -/, pattern) =>
          withLocalDeclD altEqDecl.userName (← mkEq discrVar pattern) fun altEqNew => do
            go (i+1) (altEqsNew.push altEqNew) (subst.push (← mkEqTrans eq altEqNew))
        | _, _ =>
        match eqType.heq?, altEqType.heq? with
        | some (_, _, _, discrVar), some (_, _ /- discr -/, _, pattern) =>
          withLocalDeclD altEqDecl.userName (← mkHEq discrVar pattern) fun altEqNew => do
            go (i+1) (altEqsNew.push altEqNew) (subst.push (← mkHEqTrans eq altEqNew))
        | _, _ =>
          throwError "internal error in `split` tactic: encountered unexpected auxiliary equalities created to generalize `match`-expression discriminant\nthis error typically occurs when the `split` tactic internal functions have been used in a new meta-program"
      else
        k altEqsNew subst
    go 0 #[] #[]

private def substDiscrEqs (mvarId : MVarId) (fvarSubst : FVarSubst) (discrEqs : Array FVarId) : MetaM MVarId := mvarId.withContext do
  let mut mvarId := mvarId
  let mut fvarSubst := fvarSubst
  for fvarId in discrEqs do
    if let .fvar fvarId := fvarSubst.apply (mkFVar fvarId) then
      let (fvarId, mvarId') ← heqToEq mvarId fvarId
      match (← substCore? mvarId' fvarId (symm := false) fvarSubst) with
      | some (fvarSubst', mvarId') => mvarId := mvarId'; fvarSubst := fvarSubst'
      | none =>
      match (← substCore? mvarId' fvarId (symm := true) fvarSubst) with
      | some (fvarSubst', mvarId') => mvarId := mvarId'; fvarSubst := fvarSubst'
      | none => mvarId := mvarId'
  return mvarId

def applyMatchSplitter (mvarId : MVarId) (matcherDeclName : Name) (us : Array Level) (params : Array Expr) (discrs : Array Expr) : MetaM (List MVarId) := do
  let some info ← getMatcherInfo? matcherDeclName | throwError "internal error in `split` tactic: `{matcherDeclName}` is not an auxiliary declaration used to encode `match`-expressions\nthis error typically occurs when the `split` tactic internal functions have been used in a new meta-program"
  let matchEqns ← Match.getEquationsFor matcherDeclName
  -- splitterPre does not have the correct universe elimination level, but this is fine, we only use it to compute the `motiveType`,
  -- and we only care about the `motiveType` arguments, and not the resulting `Sort u`.
  let splitterPre := mkAppN (mkConst matchEqns.splitterName us.toList) params
  let motiveType := (← whnfForall (← inferType splitterPre)).bindingDomain!
  trace[split.debug] "applyMatchSplitter\n{mvarId}"
  let (discrFVarIds, discrEqs, mvarId) ← generalizeMatchDiscrs mvarId matcherDeclName motiveType discrs
  trace[split.debug] "after generalizeMatchDiscrs\n{mvarId}"
  let mvarId ← generalizeTargetsEq mvarId motiveType (discrFVarIds.map mkFVar)
  mvarId.withContext do trace[split.debug] "discrEqs after generalizeTargetsEq: {discrEqs.map mkFVar}"
  trace[split.debug] "after generalize\n{mvarId}"
  let numEqs := discrs.size
  let (discrFVarIdsNew, mvarId) ← mvarId.introN discrs.size
  trace[split.debug] "after introN\n{mvarId}"
  let discrsNew := discrFVarIdsNew.map mkFVar
  let mvarType ← mvarId.getType
  let elimUniv ← mvarId.withContext <| getLevel mvarType
  let us ← if let some uElimPos := info.uElimPos? then
    pure <| us.set! uElimPos elimUniv
  else
    unless elimUniv.isZero do
      throwError "`split` tactic failed to split a match-expression: the splitter auxiliary theorem `{matchEqns.splitterName}` can only eliminate into `Prop`"
    pure us
  let splitter := mkAppN (mkConst matchEqns.splitterName us.toList) params
  mvarId.withContext do
    let motive ← mkLambdaFVars discrsNew mvarType
    let splitter := mkAppN (mkApp splitter motive) discrsNew
    check splitter
    trace[split.debug] "after check splitter"
    let mvarIds ← mvarId.apply splitter
    unless mvarIds.length == matchEqns.size do
      throwError "internal error in `split` tactic: unexpected number of goals created after applying splitter auxiliary theorem `{matchEqns.splitterName}` for `{matcherDeclName}`"
    let (_, mvarIds) ← mvarIds.foldlM (init := (0, [])) fun (i, mvarIds) mvarId => do
      let numParams := matchEqns.splitterAltNumParams[i]!
      let (_, mvarId) ← mvarId.introN numParams
      trace[split.debug] "before unifyEqs\n{mvarId}"
      match (← Cases.unifyEqs? (numEqs + info.getNumDiscrEqs) mvarId {}) with
      | none   => return (i+1, mvarIds) -- case was solved
      | some (mvarId, fvarSubst) =>
        trace[split.debug] "after unifyEqs\n{mvarId}"
        let mvarId ← substDiscrEqs mvarId fvarSubst discrEqs
        return (i+1, mvarId::mvarIds)
    return mvarIds.reverse

def mkDiscrGenErrorMsg (e : Expr) : MessageData :=
  m!"`split` tactic failed to generalize discriminant(s) at{indentExpr e}\nresulting expression was not type correct\npossible solution: generalize discriminant(s) manually before using `split`"

def throwDiscrGenError (e : Expr) : MetaM α :=
  throwError (mkDiscrGenErrorMsg e)

def splitMatch (mvarId : MVarId) (e : Expr) : MetaM (List MVarId) := mvarId.withContext do
  let some app ← matchMatcherApp? e | throwError "internal error in `split` tactic: match application expected{indentExpr e}\nthis error typically occurs when the `split` tactic internal functions have been used in a new meta-program"
  let matchEqns ← Match.getEquationsFor app.matcherName
  let mvarIds ← applyMatchSplitter mvarId app.matcherName app.matcherLevels app.params app.discrs
  let (_, mvarIds) ← mvarIds.foldlM (init := (0, [])) fun (i, mvarIds) mvarId => do
    let mvarId ← simpMatchTargetCore mvarId app.matcherName matchEqns.eqnNames[i]!
    return (i+1, mvarId::mvarIds)
  return mvarIds.reverse

end Split

open Split

partial def splitTarget? (mvarId : MVarId) (splitIte := true) : MetaM (Option (List MVarId)) := commitWhenSome? do mvarId.withContext do
  let target ← instantiateMVars (← mvarId.getType)
  let rec go (badCases : ExprSet) : MetaM (Option (List MVarId)) := do
    if let some e ← findSplit? target (if splitIte then .both else .match) badCases then
      if e.isIte || e.isDIte then
        return (← splitIfTarget? mvarId).map fun (s₁, s₂) => [s₁.mvarId, s₂.mvarId]
      else
        try
          splitMatch mvarId e
        catch ex =>
          if isDiscrGenException ex then
            trace[split.failure] mkDiscrGenErrorMsg e
          else
            trace[split.failure] "`split` tactic failed at{indentExpr e}\n{ex.toMessageData}"
          go (badCases.insert e)
    else
      trace[split.debug] "did not find term to split\n{MessageData.ofGoal mvarId}"
      return none
  go {}

def splitLocalDecl? (mvarId : MVarId) (fvarId : FVarId) : MetaM (Option (List MVarId)) := commitWhenSome? do
  mvarId.withContext do
    if let some e ← findSplit? (← instantiateMVars (← inferType (mkFVar fvarId))) then
      if e.isIte || e.isDIte then
        return (← splitIfLocalDecl? mvarId fvarId).map fun (mvarId₁, mvarId₂) => [mvarId₁, mvarId₂]
      else
        let result? ← commitWhenSome? do try
          let (fvarIds, mvarId) ← mvarId.revert #[fvarId]
          let num := fvarIds.size
          let mvarIds ← splitMatch mvarId e
          let mvarIds ← mvarIds.mapM fun mvarId => return (← mvarId.introNP num).2
          return some mvarIds
        catch ex =>
          if isDiscrGenException ex then
            return none
          else
            throw ex
        if result?.isSome then
          return result?
        -- Generalization failed, if `fvarId` is a let-decl or has forward dependencies, we try to `assert` a copy and try again
        let localDecl ← fvarId.getDecl
        if (← pure localDecl.isLet <||> exprDependsOn (← mvarId.getType) fvarId <||> fvarId.hasForwardDeps) then
          try
            let mvarId ← mvarId.assert localDecl.userName localDecl.type localDecl.toExpr
            let mvarIds ← splitMatch mvarId e
            let mvarIds ← mvarIds.mapM fun mvarId => return (← mvarId.intro1P).2
            return some mvarIds
          catch ex =>
            if isDiscrGenException ex then
              throwDiscrGenError e
            else
              throw ex
        throwDiscrGenError e
    else
      return none

builtin_initialize
  registerTraceClass `split.debug
  registerTraceClass `split.failure

end Lean.Meta
