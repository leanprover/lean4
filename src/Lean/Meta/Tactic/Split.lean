/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Simp.Main
import Lean.Meta.Tactic.SplitIf
import Lean.Meta.Tactic.Apply
import Lean.Meta.Tactic.Generalize

namespace Lean.Meta
namespace Split

def getSimpMatchContext : MetaM Simp.Context :=
   return {
      simpTheorems   := {}
      congrTheorems := (← getSimpCongrTheorems)
      config        := { Simp.neutralConfig with dsimp := false }
   }

def simpMatch (e : Expr) : MetaM Simp.Result := do
  (·.1) <$> Simp.main e (← getSimpMatchContext) (methods := { pre })
where
  pre (e : Expr) : SimpM Simp.Step := do
    let some app ← matchMatcherApp? e | return Simp.Step.visit { expr := e }
    -- First try to reduce matcher
    match (← reduceRecMatcher? e) with
    | some e' => return Simp.Step.done { expr := e' }
    | none    =>
      match (← Simp.simpMatchCore? app e SplitIf.discharge?) with
      | some r => return r
      | none => return Simp.Step.visit { expr := e }

def simpMatchTarget (mvarId : MVarId) : MetaM MVarId := mvarId.withContext do
  let target ← instantiateMVars (← mvarId.getType)
  let r ← simpMatch target
  applySimpResultToTarget mvarId target r

private def simpMatchCore (matchDeclName : Name) (matchEqDeclName : Name) (e : Expr) : MetaM Simp.Result := do
  (·.1) <$> Simp.main e (← getSimpMatchContext) (methods := { pre })
where
  pre (e : Expr) : SimpM Simp.Step := do
    if e.isAppOf matchDeclName then
      -- First try to reduce matcher
      match (← reduceRecMatcher? e) with
      | some e' => return Simp.Step.done { expr := e' }
      | none    =>
      -- Try lemma
      let simpTheorem := {
        origin := .decl matchEqDeclName
        proof := mkConst matchEqDeclName
        rfl := (← isRflTheorem matchEqDeclName)
      }
      match (← withReducible <| Simp.tryTheorem? e simpTheorem SplitIf.discharge?) with
      | none => return Simp.Step.visit { expr := e }
      | some r => return Simp.Step.done r
    else
      return Simp.Step.visit { expr := e }

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
          if !e.isAppOf matcherDeclName || e.getAppNumArgs != matcherInfo.arity then
            return .continue
          let some matcherApp ← matchMatcherApp? e | return .continue
          for matcherDiscr in matcherApp.discrs, discr in discrs do
            unless matcherDiscr == discr do
              trace[Meta.Tactic.split] "discr mismatch {matcherDiscr} != {discr}"
              return .continue
          let matcherApp := { matcherApp with discrs := discrVars }
          foundRef.set true
          let mut altsNew := #[]
          for i in [:matcherApp.alts.size] do
            let alt := matcherApp.alts[i]!
            let altNumParams := matcherApp.altNumParams[i]!
            let altNew ← lambdaTelescope alt fun xs body => do
              if xs.size < altNumParams || xs.size < numDiscrEqs then
                throwError "'applyMatchSplitter' failed, unexpected `match` alternative"
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
        throwError "'applyMatchSplitter' failed, did not find discriminants"
      let targetNew ← mkForallFVars (discrVars ++ eqs) targetNew
      unless (← isTypeCorrect targetNew) do
        throwError "'applyMatchSplitter' failed, failed to generalize target"
      return (targetNew, rfls)
    let mvarNew ← mkFreshExprSyntheticOpaqueMVar targetNew (← mvarId.getTag)
    trace[Meta.Tactic.split] "targetNew:\n{mvarNew.mvarId!}"
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
          throwError "'applyMatchSplitter' failed, unexpected discriminant equalities"
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
  let some info ← getMatcherInfo? matcherDeclName | throwError "'applyMatchSplitter' failed, '{matcherDeclName}' is not a 'match' auxiliary declaration."
  let matchEqns ← Match.getEquationsFor matcherDeclName
  -- splitterPre does not have the correct universe elimination level, but this is fine, we only use it to compute the `motiveType`,
  -- and we only care about the `motiveType` arguments, and not the resulting `Sort u`.
  let splitterPre := mkAppN (mkConst matchEqns.splitterName us.toList) params
  let motiveType := (← whnfForall (← inferType splitterPre)).bindingDomain!
  trace[Meta.Tactic.split] "applyMatchSplitter\n{mvarId}"
  let (discrFVarIds, discrEqs, mvarId) ← generalizeMatchDiscrs mvarId matcherDeclName motiveType discrs
  trace[Meta.Tactic.split] "after generalizeMatchDiscrs\n{mvarId}"
  let mvarId ← generalizeTargetsEq mvarId motiveType (discrFVarIds.map mkFVar)
  mvarId.withContext do trace[Meta.Tactic.split] "discrEqs after generalizeTargetsEq: {discrEqs.map mkFVar}"
  trace[Meta.Tactic.split] "after generalize\n{mvarId}"
  let numEqs := discrs.size
  let (discrFVarIdsNew, mvarId) ← mvarId.introN discrs.size
  trace[Meta.Tactic.split] "after introN\n{mvarId}"
  let discrsNew := discrFVarIdsNew.map mkFVar
  let mvarType ← mvarId.getType
  let elimUniv ← mvarId.withContext <| getLevel mvarType
  let us ← if let some uElimPos := info.uElimPos? then
    pure <| us.set! uElimPos elimUniv
  else
    unless elimUniv.isZero do
      throwError "match-splitter can only eliminate into `Prop`"
    pure us
  let splitter := mkAppN (mkConst matchEqns.splitterName us.toList) params
  mvarId.withContext do
    let motive ← mkLambdaFVars discrsNew mvarType
    let splitter := mkAppN (mkApp splitter motive) discrsNew
    check splitter
    trace[Meta.Tactic.split] "after check splitter"
    let mvarIds ← mvarId.apply splitter
    unless mvarIds.length == matchEqns.size do
      throwError "'applyMatchSplitter' failed, unexpected number of goals created after applying splitter for '{matcherDeclName}'."
    let (_, mvarIds) ← mvarIds.foldlM (init := (0, [])) fun (i, mvarIds) mvarId => do
      let numParams := matchEqns.splitterAltNumParams[i]!
      let (_, mvarId) ← mvarId.introN numParams
      trace[Meta.Tactic.split] "before unifyEqs\n{mvarId}"
      match (← Cases.unifyEqs? (numEqs + info.getNumDiscrEqs) mvarId {}) with
      | none   => return (i+1, mvarIds) -- case was solved
      | some (mvarId, fvarSubst) =>
        trace[Meta.Tactic.split] "after unifyEqs\n{mvarId}"
        let mvarId ← substDiscrEqs mvarId fvarSubst discrEqs
        return (i+1, mvarId::mvarIds)
    return mvarIds.reverse

def splitMatch (mvarId : MVarId) (e : Expr) : MetaM (List MVarId) := do
  try
    let some app ← matchMatcherApp? e | throwError "match application expected"
    let matchEqns ← Match.getEquationsFor app.matcherName
    let mvarIds ← applyMatchSplitter mvarId app.matcherName app.matcherLevels app.params app.discrs
    let (_, mvarIds) ← mvarIds.foldlM (init := (0, [])) fun (i, mvarIds) mvarId => do
      let mvarId ← simpMatchTargetCore mvarId app.matcherName matchEqns.eqnNames[i]!
      return (i+1, mvarId::mvarIds)
    return mvarIds.reverse
  catch ex =>
    throwNestedTacticEx `splitMatch ex

/-- Return an `if-then-else` or `match-expr` to split. -/
partial def findSplit? (env : Environment) (e : Expr) (splitIte := true) (exceptionSet : ExprSet := {}) : Option Expr :=
  go e
where
  go (e : Expr) : Option Expr :=
    if let some target := e.find? isCandidate then
      if e.isIte || e.isDIte then
        let cond := target.getArg! 1 5
        -- Try to find a nested `if` in `cond`
        go cond |>.getD target
      else
        some target
    else
      none

  isCandidate (e : Expr) : Bool := Id.run do
    if exceptionSet.contains e then
      false
    else if splitIte && (e.isIte || e.isDIte) then
      !(e.getArg! 1 5).hasLooseBVars
    else if let some info := isMatcherAppCore? env e then
      let args := e.getAppArgs
      for i in [info.getFirstDiscrPos : info.getFirstDiscrPos + info.numDiscrs] do
        if args[i]!.hasLooseBVars then
          return false
      return true
    else
      false

end Split

open Split

partial def splitTarget? (mvarId : MVarId) (splitIte := true) : MetaM (Option (List MVarId)) := commitWhenSome? do
  let target ← instantiateMVars (← mvarId.getType)
  let rec go (badCases : ExprSet) : MetaM (Option (List MVarId)) := do
    if let some e := findSplit? (← getEnv) target splitIte badCases then
      if e.isIte || e.isDIte then
        return (← splitIfTarget? mvarId).map fun (s₁, s₂) => [s₁.mvarId, s₂.mvarId]
      else
        try
          splitMatch mvarId e
        catch _ =>
          go (badCases.insert e)
    else
      trace[Meta.Tactic.split] "did not find term to split\n{MessageData.ofGoal mvarId}"
      return none
  go {}

def splitLocalDecl? (mvarId : MVarId) (fvarId : FVarId) : MetaM (Option (List MVarId)) := commitWhenSome? do
  mvarId.withContext do
    if let some e := findSplit? (← getEnv) (← instantiateMVars (← inferType (mkFVar fvarId))) then
      if e.isIte || e.isDIte then
        return (← splitIfLocalDecl? mvarId fvarId).map fun (mvarId₁, mvarId₂) => [mvarId₁, mvarId₂]
      else
        let (fvarIds, mvarId) ← mvarId.revert #[fvarId]
        let num := fvarIds.size
        let mvarIds ← splitMatch mvarId e
        let mvarIds ← mvarIds.mapM fun mvarId => return (← mvarId.introNP num).2
        return some mvarIds
    else
      return none

builtin_initialize registerTraceClass `Meta.Tactic.split

end Lean.Meta
