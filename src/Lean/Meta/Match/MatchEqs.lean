/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.Match.Match
public import Lean.Meta.Match.MatchEqsExt
import Lean.Meta.Tactic.Refl
import Lean.Meta.Tactic.Delta
import Lean.Meta.Tactic.CasesOnStuckLHS
import Lean.Meta.SplitSparseCasesOn
import Lean.Meta.Match.SimpH
import Lean.Meta.Match.AltTelescopes
import Lean.Meta.Match.NamedPatterns
import Lean.Meta.Match.Grind
import Lean.Meta.Match.SolveOverlap
import Lean.Meta.Eqns

public section

namespace Lean.Meta.Match

register_builtin_option debug.Meta.Match.MatchEqs.grindAsSorry : Bool := {
  defValue := false
  descr := "When proving match equations, skip running `grind`"
}

register_builtin_option bootstrap.grindInMatchEqns : Bool := {
  defValue := true
  descr := "When set to false, match equation avoids using `grind` and uses a simple \
    incomplete and inefficient approximation of it"
}

private def unfoldElimOffset (mvarId : MVarId) : MetaM MVarId := do
  if Option.isNone <| (← mvarId.getType).find? fun e => e.isConstOf ``Nat.elimOffset then
    throwError "goal's target does not contain `Nat.elimOffset`"
  mvarId.deltaTarget (· == ``Nat.elimOffset)

partial def proveCondEqThmByRefl  (type : Expr) : MetaM (Option Expr) := observing? <| withLCtx {} {} do
  let type ← instantiateMVars type
  let mvar0  ← mkFreshExprSyntheticOpaqueMVar type
  (← mvar0.mvarId!.intros).2.refl
  instantiateMVars mvar0

private def throwMatchEqnFailedMessage (matchDeclName : Name) (thmName : Name) (mvarId : MVarId) : MetaM α := do
  trace[Meta.Match.matchEqs] "gave up at:\n{mvarId}"
  throwError m!"failed to generate equality theorem {thmName} for `match` expression `{matchDeclName}`" ++
    .hint' "It may help to include indices of inductive types as discriminants in the `match` expression."

private def shouldUseGrind : MetaM Bool := do
  if !bootstrap.grindInMatchEqns.get (← getOptions) then
    return false
  -- Temporary until we can rebuild stage0 and set bootstrap.grindInMatchEqns
  -- in bootstrapping options
  if ((← getEnv).getModuleIdx? `Init).isNone then
    return false
  return true

private def solveWithGrind (mvarId : MVarId) : MetaM Unit := do
  if debug.Meta.Match.MatchEqs.grindAsSorry.get (← getOptions) then
    trace[Meta.Match.matchEqs] "proveCondEqThm.go: grind_as_sorry is enabled, admitting goal"
    mvarId.admit (synthetic := true)
    return

  if (← shouldUseGrind) then
    Match.grind mvarId
  else
    grindFallback mvarId
  trace[Meta.Match.matchEqs] "solved by grind"

private def splitIfAtHEq? (mvarId : MVarId) : MetaM (Option (MVarId × MVarId)) := mvarId.withContext do
  let type ← mvarId.getType
  let some (α,lhs,β,rhs) := type.heq? | return none
  match_expr lhs.getAppPrefix 5 with
  | dite α' cond inst «then» «else» =>
    let extraArgs := lhs.getAppArgs[5:]
    let motive := .lam `lhs α' (binderInfo := .default) <|
      mkApp4 type.getAppFn α (mkAppN (.bvar 0) extraArgs) β rhs
    -- Check the local context for conditions we can use to rewrite instead of split
    for d in (← getLCtx) do
      if (← withReducible <| isDefEq cond d.type) then
        let e := mkConst ``dif_pos [← getLevel α']
        let e := mkApp6 e cond inst d.toExpr α' «then» «else»
        let e ← mkCongrArg motive e
        let mvarId' ← mvarId.replaceTargetEq (motive.beta #[«then».beta #[d.toExpr]]) e
        return #[mvarId']
      if (← withReducible <| isDefEq (mkNot cond) d.type) then
        let e := mkConst ``dif_neg [← getLevel α']
        let e := mkApp6 e cond inst d.toExpr α' «then» «else»
        let e ← mkCongrArg motive e
        let mvarId' ← mvarId.replaceTargetEq (motive.beta #[«else».beta #[d.toExpr]]) e
        return #[mvarId']
    let e := mkConst `diteInduction [← getLevel α', ← getLevel type]
    let e := mkApp6 e α' cond inst motive «then» «else»
    let [mvarId₁, mvarId₂] ← mvarId.applyN e 2 | panic! "splitIfAtHEq: unexpected number of subgoals"
    let (fvarId₁, mvarId₁) ← mvarId₁.intro1
    let mvarId₁ ← trySubst mvarId₁ fvarId₁
    let (_, mvarId₂) ← mvarId₂.intro1
    return #[mvarId₁, mvarId₂]
  | _ => throwError "rwOrSplitIfAtHEq?: LHS is not a `dite` application"

private partial def proveCongrEqThm (matchDeclName : Name) (thmName : Name) (mvarId : MVarId) : MetaM Unit := do
  withTraceNode `Meta.Match.matchEqs (msg := (return m!"{exceptEmoji ·} proveCongrEqThm {thmName}")) do
  let mvarId ← mvarId.deltaTarget (· == matchDeclName)
  go mvarId 0
where
  go (mvarId : MVarId) (depth : Nat) : MetaM Unit := withIncRecDepth do
    trace[Meta.Match.matchEqs] "proveCongrEqThm.go {mvarId}"
    let mvarId ← mvarId.modifyTargetEqLHS whnfCore
    let subgoals ←
      (do let mvarId ← unfoldElimOffset mvarId; return #[mvarId])
      <|>
      (casesOnStuckLHS mvarId)
      <|>
      (reduceSparseCasesOn mvarId)
      <|>
      (splitSparseCasesOn mvarId)
      <|>
      (rwOrSplitIfAtHEq? mvarId)
      <|>
      (goLeaf mvarId *> return #[])
    subgoals.forM (go · (depth+1))

  goLeaf (mvarId : MVarId) : MetaM Unit := do
    -- At this point we should have a leave goal
    trace[Meta.Match.matchEqs] "proveCongrEqThm.goLeaf{indentD mvarId}"
    let type ← instantiateMVars (← mvarId.getType)
    let badLeafGoal := mvarId.withContext do
      throwError "Incomplete case splitting during match compilation, goal left-hand side not fully \
        reduced to an application of a match alternative:{indentExpr type}"
    let some (_, lhs, _, rhs) := type.heq? | badLeafGoal
    let .fvar lhsFn := lhs.getAppFn | badLeafGoal
    let .fvar rhsFn := rhs.getAppFn | badLeafGoal

    if lhsFn == rhsFn then
      (solveWithGrind mvarId)
      <|>
      (throwMatchEqnFailedMessage matchDeclName thmName mvarId)
    else
      let mvarId ← mvarId.exfalso
      solveWithGrind mvarId
      <|>
      -- We need contradiction only for genDiseq. We could be smart about recognizing
      -- the right assumption to use here, and call processGenDiseq directly, avoiding
      -- contradiction
      (do mvarId.contradiction { genDiseq := true }
          trace[Meta.Match.matchEqs] "solved by contradiction")
      <|>
      (throwMatchEqnFailedMessage matchDeclName thmName mvarId)

/--
Given an application of an matcher arm `alt` that is expecting the `numDiscrEqs`, and
an array of `discr = pattern` equalities (one for each discriminant), apply those that
are expected by the alternative.
-/
partial def mkAppDiscrEqs (alt : Expr) (heqs : Array Expr) (numDiscrEqs : Nat) : MetaM Expr := do
  go alt (← inferType alt) 0
where
  go e ty i := do
    if i < numDiscrEqs then
      let Expr.forallE n d b .. := ty
        | throwError "expecting {numDiscrEqs} equalities, but found type{indentExpr alt}"
      for heq in heqs do
        if (← isDefEq (← inferType heq) d) then
          return ← go (mkApp e heq) (b.instantiate1 heq) (i+1)
      throwError "Could not find equation {n} : {d} among {heqs}"
    else
      return e

private def genNotAltType (matchInfo : MatcherInfo) (discrs : Array Expr) (alts : Array Expr) (i : Nat) : MetaM Expr := do
  let alt := alts[i]!
  let altInfo := matchInfo.altInfos[i]!
  let altType ← inferType alt
  Match.forallAltVarsTelescope altType altInfo fun altVars _args _mask altResultType => do
    let patterns ← forallTelescope altResultType fun _ t => pure t.getAppArgs
    let mut notAlt := mkConst ``False
    for discr in discrs.reverse, pattern in patterns.reverse do
      notAlt ← mkArrow (← mkEqHEq discr pattern) notAlt
    mkForallFVars altVars notAlt

def genMatchCongrEqn (matchDeclName : Name) (i : Nat) : MetaM Name := do
  let some matchInfo ← getMatcherInfo? matchDeclName | throwError "`{matchDeclName}` is not a matcher function"
  unless (i < matchInfo.numAlts) do
    throwError "index {i} is out of bounds for alternatives of matcher `{matchDeclName}`"
  let baseName := mkPrivateName (← getEnv) matchDeclName
  let thmName := (baseName.str congrEqnThmSuffixBase).appendIndexAfter (i + 1)
  realizeConst matchDeclName thmName (go thmName)
  return thmName
where go thmName :=
  withoutExporting do
  withConfig (fun c => { c with etaStruct := .none }) do
  trace[Meta.Match.matchEqs] "genMatchCongrEqnsImpl on {matchDeclName}"
  let constInfo ← getConstInfo matchDeclName
  let us := constInfo.levelParams.map mkLevelParam
  let some matchInfo ← getMatcherInfo? matchDeclName | throwError "`{matchDeclName}` is not a matcher function"
  let numDiscrEqs := matchInfo.getNumDiscrEqs
  forallTelescopeReducing constInfo.type fun xs _matchResultType => do
    let mut eqnNames := #[]
    let params : Array Expr := xs[*...matchInfo.numParams]
    let motive              := xs[matchInfo.getMotivePos]!
    let alts   : Array Expr := xs[(xs.size - matchInfo.numAlts)...*]
    let firstDiscrIdx       := matchInfo.numParams + 1
    let discrs : Array Expr := xs[firstDiscrIdx...(firstDiscrIdx + matchInfo.numDiscrs)]
    let altInfo := matchInfo.altInfos[i]!
    trace[Meta.Match.matchEqs] "genMatchCongrEqn working on {thmName}"
    eqnNames := eqnNames.push thmName
    do
      let alt := alts[i]!
      let altType ← inferType alt
      Match.forallAltVarsTelescope altType altInfo fun altVars args _mask altResultType => do
      let patterns ← forallTelescope altResultType fun _ t => pure t.getAppArgs
      let mut heqsTypes := #[]
      assert! patterns.size == discrs.size
      for discr in discrs, pattern in patterns do
        let heqType ← mkEqHEq discr pattern
        heqsTypes := heqsTypes.push heqType
      withLocalDeclsDND' `heq heqsTypes fun heqs => do
        let rhs ← Match.mkAppDiscrEqs (mkAppN alt args) heqs numDiscrEqs
        let overlappedBys : Array Nat := matchInfo.overlaps.overlapping i
        let hs_discr ← overlappedBys.mapM fun overlappedBy => do
          -- we need to start with the overlap assumptions applid to the abstract
          -- discriminants, so that they are picked up reliably by `contradiction`
          -- We later simplify them to expose the them applied to the patterns
          -- to match what the splitter provides
          genNotAltType matchInfo discrs alts overlappedBy
        trace[Meta.Match.matchEqs] "hs (abstract): {hs_discr}"
        let thmVal ← withLocalDeclsDND' `hnot hs_discr fun hs_discrs => do
          let lhs := mkAppN (mkConst constInfo.name us) (params ++ #[motive] ++ discrs ++ alts)
          let thmType ← mkHEq lhs rhs
          let thmType ← unfoldNamedPattern thmType
          let thmVal  ← mkFreshExprSyntheticOpaqueMVar thmType
          let mvarId := thmVal.mvarId!
          ( do -- Fast path trying refl if there are no overlaps assumptions
              unless hs_discrs.isEmpty do
                throwError "cannot use refl when there are overlap assumptions"
              let mut mvarId := mvarId
              (_, mvarId) ← mvarId.revert (heqs.map Expr.fvarId!) (preserveOrder := true)
              trace[Meta.Match.matchEqs] "reverted:\n{mvarId}"
              -- TODO: Code duplication with below
              for _ in [:heqs.size] do
                let (fvarId, mvarId') ← mvarId.intro1
                (_, mvarId) ← substEq mvarId' fvarId
              mvarId ← mvarId.heqOfEq
              mvarId.refl)
          -- Default path
          <|> proveCongrEqThm matchDeclName thmName mvarId
          let thmVal ← mkExpectedTypeHint thmVal thmType
          let thmVal ← instantiateMVars thmVal
          mkLambdaFVars hs_discrs thmVal
        -- Now we simplify the overlap assumptions
        let hs_discr ← hs_discr.mapM mkFreshExprSyntheticOpaqueMVar
        let thmVal := mkAppN thmVal hs_discr
        let hs_pat : Array MVarId ←
          withTraceNode `Meta.Match.matchEqs (msg := (return m!"{exceptEmoji ·} simplify overlap assumptions")) do
          hs_discr.filterMapM fun h_discr => do
            let mut mvarId' := h_discr.mvarId!
            trace[Meta.Match.matchEqs] "before subst: {mvarId'}"
            mvarId' := (← mvarId'.revert (heqs.map (·.fvarId!)) (preserveOrder := true)).2
            -- always good to clear before substing
            mvarId' ← mvarId'.tryClearMany <| (#[motive] ++ alts ++ heqs).map (·.fvarId!)
            for _ in [:heqs.size] do
              let (fvarId, mvarId'') ← mvarId'.intro1
              -- important to substitute the fvar on the LHS, so do not use `substEq`
              let (fvarId, mvarId'') ← heqToEq mvarId'' fvarId
              (_, mvarId') ← substCore (symm := false) (clearH := true) mvarId'' fvarId
            trace[Meta.Match.matchEqs] "after subst: {mvarId'}"
            let r ← simpH mvarId' discrs.size
            trace[Meta.Match.matchEqs] "after simpH: {r}"
            pure r
        let thmVal ← withLocalDeclsDND' `hnot (← hs_pat.mapM (·.getType)) fun xs => do
          for h_pat in hs_pat, x in xs do h_pat.assign x
          mkLambdaFVars xs (← instantiateMVars thmVal)
        let thmVal ← mkLambdaFVars (params ++ #[motive] ++ discrs ++ alts ++ altVars ++ heqs) thmVal
        let thmType ← inferType thmVal
        let thmType ← unfoldNamedPattern thmType
        unless (← getEnv).contains thmName do
          addDecl <| Declaration.thmDecl {
            name        := thmName
            levelParams := constInfo.levelParams
            type        := thmType
            value       := thmVal
          }

/--
  Create new alternatives (aka minor premises) by replacing `discrs` with `patterns` at `alts`.
  Recall that `alts` depends on `discrs` when `numDiscrEqs > 0`, where `numDiscrEqs` is the number of discriminants
  annotated with `h : discr`.
-/
private partial def withNewAlts (numDiscrEqs : Nat) (discrs : Array Expr) (patterns : Array Expr) (alts : Array Expr) (k : Array Expr → MetaM α) : MetaM α :=
  if numDiscrEqs == 0 then
    k alts
  else
    go 0 #[]
where
  go (i : Nat) (altsNew : Array Expr) : MetaM α := do
   if h : i < alts.size then
     let altLocalDecl ← getFVarLocalDecl alts[i]
     let typeNew := altLocalDecl.type.replaceFVars discrs patterns
     withLocalDecl altLocalDecl.userName altLocalDecl.binderInfo typeNew fun altNew =>
       go (i+1) (altsNew.push altNew)
   else
     k altsNew

/-
Creates conditional equations and splitter for the given match auxiliary declaration.

See also `getEquationsFor`.
-/
@[export lean_get_match_equations_for]
def getEquationsForImpl (matchDeclName : Name) : MetaM MatchEqns := do
  /-
  Remark: users have requested the `split` tactic to be available for writing code.
  Thus, the `splitter` declaration must be a definition instead of a theorem.
  Moreover, the `splitter` is generated on demand, and we currently
  can't import the same definition from different modules. Thus, we must
  keep `splitter` as a private declaration to prevent import failures.
  -/
  let baseName := mkPrivateName (← getEnv) matchDeclName
  let splitterName := baseName ++ `splitter
  -- NOTE: `go` will generate both splitter and equations but we use the splitter as the "key" for
  -- `realizeConst` as well as for looking up the resultant environment extension state via
  -- `getState`.
  realizeConst matchDeclName splitterName (go baseName splitterName)
  match matchEqnsExt.getState (asyncMode := .async .asyncEnv) (asyncDecl := splitterName) (← getEnv) |>.map.find? matchDeclName with
  | some eqns => return eqns
  | none      => throwError "failed to retrieve match equations for `{matchDeclName}` after realization"
where go baseName splitterName := withConfig (fun c => { c with etaStruct := .none }) do
  let constInfo ← getConstInfo matchDeclName
  let us := constInfo.levelParams.map mkLevelParam
  let some matchInfo ← getMatcherInfo? matchDeclName | throwError "`{matchDeclName}` is not a matcher function"
  let numDiscrEqs := getNumEqsFromDiscrInfos matchInfo.discrInfos
  forallTelescopeReducing constInfo.type fun xs _matchResultType => do
    let mut eqnNames := #[]
    let params : Array Expr := xs[*...matchInfo.numParams]
    let motive : Expr       := xs[matchInfo.getMotivePos]!
    let alts   : Array Expr := xs[(xs.size - matchInfo.numAlts)...*]
    let firstDiscrIdx       := matchInfo.numParams + 1
    let discrs : Array Expr := xs[firstDiscrIdx...(firstDiscrIdx + matchInfo.numDiscrs)]
    let mut splitterAltInfos := #[]
    for i in *...alts.size do
      let thmName := Name.str baseName eqnThmSuffixBase |>.appendIndexAfter (i + 1)
      trace[Meta.Match.matchEqs] "proving {thmName}"
      let altInfo := matchInfo.altInfos[i]!
      eqnNames := eqnNames.push thmName
      let splitterAltInfo ← forallAltTelescope (← inferType alts[i]!) altInfo numDiscrEqs
          fun ys rhsArgs altResultType => do
        let patterns := altResultType.getAppArgs
        let hs ← (matchInfo.overlaps.overlapping i).filterMapM fun overlappedBy => do
          let h ← genNotAltType matchInfo discrs alts overlappedBy
          let h := h.replaceFVars discrs patterns
          simpH? h patterns.size
        trace[Meta.Match.matchEqs] "hs: {hs}"
        let hasUnitThunk := ys.isEmpty && hs.isEmpty && numDiscrEqs = 0
        let splitterAltInfo := { numFields := ys.size, numOverlaps := hs.size, hasUnitThunk }
        /- Recall that when we use the `h : discr`, the alternative type depends on the discriminant.
           Thus, we need to create new `alts`. -/
        withNewAlts numDiscrEqs discrs patterns alts fun alts => do
        withLocalDeclsDND' `notAlt hs fun hs => do
          let alt := alts[i]!
          let lhs := mkAppN (mkConst constInfo.name us) (params ++ #[motive] ++ patterns ++ alts)
          let rhs := mkAppN alt rhsArgs
          let thmType ← mkEq lhs rhs
          let thmType ← mkForallFVars (params ++ #[motive] ++ ys ++ alts ++ hs) thmType
          let thmType ← unfoldNamedPattern thmType
          let thmVal ←
            if let some thmVal ← proveCondEqThmByRefl thmType then
              trace[Meta.Match.matchEqs] "proved equation {thmName} by refl"
              pure thmVal
            else
              let congrEqThm ← genMatchCongrEqn matchDeclName i
              let thmVal := mkConst congrEqThm us
              -- We build the normal equation from the congruence equation here
              let thmVal := mkAppN thmVal (params ++ #[motive] ++ patterns ++ alts ++ ys)
              let eqTypes ← inferArgumentTypesN discrs.size thmVal
              let eqProofs ← eqTypes.mapM fun eqType => do
                let a ← mkFreshExprSyntheticOpaqueMVar eqType
                (← a.mvarId!.heqOfEq).refl
                pure a
              let thmVal := mkAppN thmVal eqProofs
              let thmVal := mkAppN thmVal hs
              let thmVal ← mkEqOfHEq thmVal
              mkLambdaFVars (params ++ #[motive] ++ ys ++ alts ++ hs) thmVal
          addDecl <| Declaration.thmDecl {
            name        := thmName
            levelParams := constInfo.levelParams
            type        := thmType
            value       := thmVal
          }
          return splitterAltInfo
      splitterAltInfos := splitterAltInfos.push splitterAltInfo
    let splitterMatchInfo : MatcherInfo := { matchInfo with altInfos := splitterAltInfos }

    let needsSplitter := !matchInfo.overlaps.isEmpty || (constInfo.type.find? (isNamedPattern )).isSome
    trace[Meta.Match.matchEqs] "needsSplitter: {needsSplitter}"

    if needsSplitter then
      withMkMatcherInput matchDeclName (unfoldNamed := true) fun matcherInput => do
        let matcherInput := { matcherInput with
          matcherName := splitterName
          isSplitter := some matchInfo.overlaps
        }
        let res ← Match.mkMatcher matcherInput
        res.addMatcher -- TODO: Do not set matcherinfo for the splitter!
    else
      assert! matchInfo.altInfos == splitterAltInfos
      -- This match statement does not need a splitter, we can use itself for that.
      -- (We still have to generate a declaration to satisfy the realizable constant)
      addAndCompile (logCompileErrors := false) <| Declaration.defnDecl {
        name        := splitterName
        levelParams := constInfo.levelParams
        type        := constInfo.type
        value       := mkConst matchDeclName us
        hints       := .abbrev
        safety      := .safe
      }
      setInlineAttribute splitterName
    let result := { eqnNames, splitterName, splitterMatchInfo }
    registerMatchEqns matchDeclName result

/--
Generate the congruence equations for the given match auxiliary declaration.
The congruence equations have a completely unrestricted left-hand side (arbitrary discriminants),
and take propositional equations relating the discriminants to the patterns as arguments. In this
sense they combine a congruence lemma with the regular equation lemma.
Since the motive depends on the discriminants, they are `HEq` equations.

The code duplicates a fair bit of the logic above, and has to repeat the calculation of the
`notAlts`. One could avoid that and generate the generalized equations eagerly above, but they are
not always needed, so for now we live with the code duplication.
-/
@[export lean_get_congr_match_equations_for]
def genMatchCongrEqnsImpl (matchDeclName : Name) : MetaM (Array Name) := do
  let some matchInfo ← getMatcherInfo? matchDeclName | throwError "`{matchDeclName}` is not a matcher function"
  let mut ns := #[]
  for i in *...matchInfo.numAlts do
    ns := ns.push (← genMatchCongrEqn matchDeclName i)
  return ns

builtin_initialize registerTraceClass `Meta.Match.matchEqs

private def isMatchEqName? (env : Environment) (n : Name) : Option (Name × Bool) := do
  let .str p s := n | failure
  guard <| isEqnReservedNameSuffix s || s == "splitter" || isCongrEqnReservedNameSuffix s
  let p ← privateToUserName? p
  guard <| isMatcherCore env p
  return (p, isCongrEqnReservedNameSuffix s)

builtin_initialize registerReservedNamePredicate (isMatchEqName? · · |>.isSome)

builtin_initialize registerReservedNameAction fun name => do
  let some (p, isGenEq) := isMatchEqName? (← getEnv) name |
    return false
  if isGenEq then
    let _ ← MetaM.run' <| genMatchCongrEqnsImpl p
  else
    let _ ← MetaM.run' <| getEquationsFor p
  return true

end Lean.Meta.Match
