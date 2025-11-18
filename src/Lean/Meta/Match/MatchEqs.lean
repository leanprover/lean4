/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.Match.Match
public import Lean.Meta.Match.MatchEqsExt
public import Lean.Meta.Tactic.Refl
public import Lean.Meta.Tactic.Delta
import Lean.Meta.Tactic.SplitIf
import Lean.Meta.Match.SimpH
import Lean.Meta.Match.SolveOverlap

public section

namespace Lean.Meta

/--
  Helper method for `proveCondEqThm`. Given a goal of the form `C.rec ... xMajor = rhs`,
  apply `cases xMajor`. -/
partial def casesOnStuckLHS (mvarId : MVarId) : MetaM (Array MVarId) := do
  let target ← mvarId.getType
  if let some (_, lhs, _) ← matchEq? target then
    if let some fvarId ← findFVar? lhs then
      return (←  mvarId.cases fvarId).map fun s => s.mvarId
  throwError "'casesOnStuckLHS' failed"
where
  findFVar? (e : Expr) : MetaM (Option FVarId) := do
    match e.getAppFn with
    | Expr.proj _ _ e => findFVar? e
    | f =>
      if !f.isConst then
        return none
      else
        let declName := f.constName!
        let args := e.getAppArgs
        match (← getProjectionFnInfo? declName) with
        | some projInfo =>
          if projInfo.numParams < args.size then
            findFVar? args[projInfo.numParams]!
          else
            return none
        | none =>
          matchConstRec f (fun _ => return none) fun recVal _ => do
            if recVal.getMajorIdx >= args.size then
              return none
            let major := args[recVal.getMajorIdx]!.consumeMData
            if major.isFVar then
              return some major.fvarId!
            else
              return none

def casesOnStuckLHS? (mvarId : MVarId) : MetaM (Option (Array MVarId)) := do
  try casesOnStuckLHS mvarId catch _ => return none

namespace Match

def unfoldNamedPattern (e : Expr) : MetaM Expr := do
  let visit (e : Expr) : MetaM TransformStep := do
    if let some e := isNamedPattern? e then
      if let some eNew ← unfoldDefinition? e then
        return TransformStep.visit eNew
    return .continue
  Meta.transform e (pre := visit)

/--
  Similar to `forallTelescopeReducing`, but

  1. Eliminates arguments for named parameters and the associated equation proofs.

  2. Instantiate the `Unit` parameter of an otherwise argumentless alternative.

  It does not handle the equality parameters associated with the `h : discr` notation.

  The continuation `k` takes four arguments `ys args mask type`.
  - `ys` are variables for the hypotheses that have not been eliminated.
  - `args` are the arguments for the alternative `alt` that has type `altType`. `ys.size <= args.size`
  - `mask[i]` is true if the hypotheses has not been eliminated. `mask.size == args.size`.
  - `type` is the resulting type for `altType`.

  We use the `mask` to build the splitter proof. See `mkSplitterProof`.

  This can be used to use the alternative of a match expression in its splitter.
-/
partial def forallAltVarsTelescope (altType : Expr) (altNumParams numDiscrEqs : Nat)
  (k : (patVars : Array Expr) → (args : Array Expr) → (mask : Array Bool) → (type : Expr) → MetaM α) : MetaM α := do
  go #[] #[] #[] 0 altType
where
  go (ys : Array Expr) (args : Array Expr) (mask : Array Bool) (i : Nat) (type : Expr) : MetaM α := do
    let type ← whnfForall type
    if i < altNumParams - numDiscrEqs then
      let Expr.forallE n d b .. := type
        | throwError "expecting {altNumParams} parameters, excluding {numDiscrEqs} equalities, but found type{indentExpr altType}"

      -- Handle the special case of `Unit` parameters.
      if i = 0 && altNumParams - numDiscrEqs = 1 && d.isConstOf ``Unit && !b.hasLooseBVars then
        return ← k #[] #[mkConst ``Unit.unit] #[false] b

      let d ← Match.unfoldNamedPattern d
      withLocalDeclD n d fun y => do
        let typeNew := b.instantiate1 y
        if let some (_, lhs, rhs) ← matchEq? d then
          if lhs.isFVar && ys.contains lhs && args.contains lhs && isNamedPatternProof typeNew y then
              let some j  := ys.finIdxOf? lhs | unreachable!
              let ys      := ys.eraseIdx j
              let some k  := args.idxOf? lhs | unreachable!
              let mask    := mask.set! k false
              let args    := args.map fun arg => if arg == lhs then rhs else arg
              let arg     ← mkEqRefl rhs
              let typeNew := typeNew.replaceFVar lhs rhs
              return ← withReplaceFVarId lhs.fvarId! rhs do
              withReplaceFVarId y.fvarId! arg do
                go ys (args.push arg) (mask.push false) (i+1) typeNew
        go (ys.push y) (args.push y) (mask.push true) (i+1) typeNew
    else
      let type ← Match.unfoldNamedPattern type
      k ys args mask type

  isNamedPatternProof (type : Expr) (h : Expr) : Bool :=
    Option.isSome <| type.find? fun e =>
      if let some e := Match.isNamedPattern? e then
        e.appArg! == h
      else
        false


/--
  Extension of `forallAltTelescope` that continues further:

  Equality parameters associated with the `h : discr` notation are replaced with `rfl` proofs.
  Recall that this kind of parameter always occurs after the parameters corresponding to pattern
  variables.

  The continuation `k` takes four arguments `ys args mask type`.
  - `ys` are variables for the hypotheses that have not been eliminated.
  - `eqs` are variables for equality hypotheses associated with discriminants annotated with `h : discr`.
  - `args` are the arguments for the alternative `alt` that has type `altType`. `ys.size <= args.size`
  - `mask[i]` is true if the hypotheses has not been eliminated. `mask.size == args.size`.
  - `type` is the resulting type for `altType`.

  We use the `mask` to build the splitter proof. See `mkSplitterProof`.

  This can be used to use the alternative of a match expression in its splitter.
-/
partial def forallAltTelescope (altType : Expr) (altNumParams numDiscrEqs : Nat)
    (k : (ys : Array Expr) → (eqs : Array Expr) → (args : Array Expr) → (mask : Array Bool) → (type : Expr) → MetaM α)
    : MetaM α := do
  forallAltVarsTelescope altType altNumParams numDiscrEqs fun ys args mask altType => do
    go ys #[] args mask 0 altType
where
  go (ys : Array Expr) (eqs : Array Expr) (args : Array Expr) (mask : Array Bool) (i : Nat) (type : Expr) : MetaM α := do
    let type ← whnfForall type
    if i < numDiscrEqs then
      let Expr.forallE n d b .. := type
        | throwError "expecting {altNumParams} parameters, including {numDiscrEqs} equalities, but found type{indentExpr altType}"
      let arg ← if let some (_, _, rhs) ← matchEq? d then
        mkEqRefl rhs
      else if let some (_, _, _, rhs) ← matchHEq? d then
        mkHEqRefl rhs
      else
        throwError "unexpected match alternative type{indentExpr altType}"
      withLocalDeclD n d fun eq => do
        let typeNew := b.instantiate1 eq
        go ys (eqs.push eq) (args.push arg) (mask.push false) (i+1) typeNew
    else
      let type ← unfoldNamedPattern type
      k ys eqs args mask type

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


private def substSomeVar (mvarId : MVarId) : MetaM (Array MVarId) := mvarId.withContext do
  for localDecl in (← getLCtx) do
    if let some (_, lhs, rhs) ← matchEq? localDecl.type then
      if lhs.isFVar then
        if !(← dependsOn rhs lhs.fvarId!) then
          match (← subst? mvarId lhs.fvarId!) with
          | some mvarId => return #[mvarId]
          | none => pure ()
  throwError "substSomeVar failed"

private def unfoldElimOffset (mvarId : MVarId) : MetaM MVarId := do
  if Option.isNone <| (← mvarId.getType).find? fun e => e.isConstOf ``Nat.elimOffset then
    throwError "goal's target does not contain `Nat.elimOffset`"
  mvarId.deltaTarget (· == ``Nat.elimOffset)

/--
Helper method for proving a conditional equational theorem associated with an alternative of
the `match`-eliminator `matchDeclName`. `type` contains the type of the theorem.

The `heqPos`/`heqNum` arguments indicate that these hypotheses are `Eq`/`HEq` hypotheses
to substitute first; this is used for the generalized match equations.
-/
partial def proveCondEqThm (matchDeclName : Name) (type : Expr)
  (heqPos : Nat := 0) (heqNum : Nat := 0) : MetaM Expr := withLCtx {} {} do
  let type ← instantiateMVars type
  let mvar0  ← mkFreshExprSyntheticOpaqueMVar type
  trace[Meta.Match.matchEqs] "proveCondEqThm {mvar0.mvarId!}"
  let mut mvarId := mvar0.mvarId!
  if heqNum > 0 then
    mvarId := (← mvarId.introN heqPos).2
    for _ in *...heqNum do
      let (h, mvarId') ← mvarId.intro1
      mvarId ← subst mvarId' h
    trace[Meta.Match.matchEqs] "proveCondEqThm after subst{mvarId}"
  mvarId := (← mvarId.intros).2
  try mvarId.refl
  catch _ =>
    mvarId ← mvarId.deltaTarget (· == matchDeclName)
    mvarId ← mvarId.heqOfEq
    go mvarId 0
  instantiateMVars mvar0
where
  go (mvarId : MVarId) (depth : Nat) : MetaM Unit := withIncRecDepth do
    trace[Meta.Match.matchEqs] "proveCondEqThm.go {mvarId}"
    let mvarId ← mvarId.modifyTargetEqLHS whnfCore
    let subgoals ←
      (do mvarId.refl; return #[])
      <|>
      (do mvarId.contradiction { genDiseq := true }; return #[])
      <|>
      (do let mvarId ← unfoldElimOffset mvarId; return #[mvarId])
      <|>
      (casesOnStuckLHS mvarId)
      <|>
      (do let mvarId' ← simpIfTarget mvarId (useDecide := true) (useNewSemantics := true)
          if mvarId' == mvarId then throwError "simpIf failed"
          return #[mvarId'])
      <|>
      (do if let some (s₁, s₂) ← splitIfTarget? mvarId (useNewSemantics := true) then
            let mvarId₁ ← trySubst s₁.mvarId s₁.fvarId
            return #[mvarId₁, s₂.mvarId]
          else
            throwError "spliIf failed")
      <|>
      (substSomeVar mvarId)
      <|>
      (throwError "failed to generate equality theorems for `match` expression `{matchDeclName}`\n{MessageData.ofGoal mvarId}")
    subgoals.forM (go · (depth+1))


/-- Construct new local declarations `xs` with types `altTypes`, and then execute `f xs`  -/
private partial def withSplitterAlts (altTypes : Array Expr) (f : Array Expr → MetaM α) : MetaM α := do
  let rec go (i : Nat) (xs : Array Expr) : MetaM α := do
    if h : i < altTypes.size then
      let hName := (`h).appendIndexAfter (i+1)
      withLocalDeclD hName altTypes[i] fun x =>
        go (i+1) (xs.push x)
    else
      f xs
  go 0 #[]

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
  forallTelescopeReducing constInfo.type fun xs matchResultType => do
    let mut eqnNames := #[]
    let params := xs[*...matchInfo.numParams]
    let motive := xs[matchInfo.getMotivePos]!
    let alts   := xs[(xs.size - matchInfo.numAlts)...*]
    let firstDiscrIdx := matchInfo.numParams + 1
    let discrs := xs[firstDiscrIdx...(firstDiscrIdx + matchInfo.numDiscrs)]
    let mut notAlts := #[]
    let mut idx := 1
    let mut splitterAltTypes := #[]
    let mut splitterAltNumParams := #[]
    let mut altArgMasks := #[] -- masks produced by `forallAltTelescope`
    for i in *...alts.size do
      let altNumParams := matchInfo.altNumParams[i]!
      let thmName := Name.str baseName eqnThmSuffixBase |>.appendIndexAfter idx
      eqnNames := eqnNames.push thmName
      let (notAlt, splitterAltType, splitterAltNumParam, argMask) ←
          forallAltTelescope (← inferType alts[i]!) altNumParams numDiscrEqs
          fun ys eqs rhsArgs argMask altResultType => do
        let patterns := altResultType.getAppArgs
        let mut hs := #[]
        for overlappedBy in matchInfo.overlaps.overlapping i do
          let notAlt := notAlts[overlappedBy]!
          let h ← instantiateForall notAlt patterns
          if let some h ← simpH? h patterns.size then
            hs := hs.push h
        trace[Meta.Match.matchEqs] "hs: {hs}"
        let splitterAltType ← mkForallFVars ys (← hs.foldrM (init := (← mkForallFVars eqs altResultType)) (mkArrow · ·))
        let splitterAltType ← unfoldNamedPattern splitterAltType
        let splitterAltNumParam := hs.size + ys.size
        -- Create a proposition for representing terms that do not match `patterns`
        let mut notAlt := mkConst ``False
        for discr in discrs.toArray.reverse, pattern in patterns.reverse do
          notAlt ← mkArrow (← mkEqHEq discr pattern) notAlt
        notAlt ← mkForallFVars (discrs ++ ys) notAlt
        /- Recall that when we use the `h : discr`, the alternative type depends on the discriminant.
           Thus, we need to create new `alts`. -/
        withNewAlts numDiscrEqs discrs patterns alts fun alts => do
          let alt := alts[i]!
          let lhs := mkAppN (mkConst constInfo.name us) (params ++ #[motive] ++ patterns ++ alts)
          let rhs := mkAppN alt rhsArgs
          let thmType ← mkEq lhs rhs
          let thmType ← hs.foldrM (init := thmType) (mkArrow · ·)
          let thmType ← mkForallFVars (params ++ #[motive] ++ ys ++ alts) thmType
          let thmType ← unfoldNamedPattern thmType
          let thmVal ← proveCondEqThm matchDeclName thmType
          addDecl <| Declaration.thmDecl {
            name        := thmName
            levelParams := constInfo.levelParams
            type        := thmType
            value       := thmVal
          }
          return (notAlt, splitterAltType, splitterAltNumParam, argMask)
      notAlts := notAlts.push notAlt
      splitterAltTypes := splitterAltTypes.push splitterAltType
      splitterAltNumParams := splitterAltNumParams.push splitterAltNumParam
      altArgMasks := altArgMasks.push argMask
      trace[Meta.Match.matchEqs] "splitterAltType: {splitterAltType}"
      idx := idx + 1

    if !matchInfo.needsSplitter then
      -- This match statement does not need a splitter, we can use itself for that.
      -- (We still have to generate a declaration to satisfy the realizable constant)
      addAndCompile <| Declaration.defnDecl {
        name        := splitterName
        levelParams := constInfo.levelParams
        type        := constInfo.type
        value       := mkConst matchDeclName us
        hints       := .abbrev
        safety      := .safe
      }
      setInlineAttribute splitterName
    else
      -- Define splitter with conditional/refined alternatives
      withSplitterAlts splitterAltTypes fun altsNew => do
        let splitterParams := params.toArray ++ #[motive] ++ discrs.toArray ++ altsNew
        let splitterType ← mkForallFVars splitterParams matchResultType
        trace[Meta.Match.matchEqs] "splitterType: {splitterType}"

        withMkMatcherInput matchDeclName (unfoldNamed := true) fun matcherInput => do
          let matcherInput := { matcherInput with
            matcherName := splitterName
            isSplitter := true
          }
          let res ← Match.mkMatcher matcherInput
          res.addMatcher -- TODO: Do not set matcherinfo for the splitter!
    let result := { eqnNames, splitterName, splitterAltNumParams }
    registerMatchEqns matchDeclName result

/- We generate the equations and splitter on demand, and do not save them on .olean files. -/
builtin_initialize matchCongrEqnsExt : EnvExtension (PHashMap Name (Array Name)) ←
  -- Using `local` allows us to use the extension in `realizeConst` without specifying `replay?`.
  -- The resulting state can still be accessed on the generated declarations using `.asyncEnv`;
  -- see below
  registerEnvExtension (pure {}) (asyncMode := .local)

def registerMatchCongrEqns (matchDeclName : Name) (eqnNames : Array Name) : CoreM Unit := do
  modifyEnv fun env => matchCongrEqnsExt.modifyState env fun map =>
    map.insert matchDeclName eqnNames

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
def genMatchCongrEqns (matchDeclName : Name) : MetaM (Array Name) := do
  let baseName := mkPrivateName (← getEnv) matchDeclName
  let firstEqnName := .str baseName congrEqn1ThmSuffix
  realizeConst matchDeclName firstEqnName (go baseName)
  return matchCongrEqnsExt.getState (asyncMode := .async .asyncEnv) (asyncDecl := firstEqnName) (← getEnv) |>.find! matchDeclName
where go baseName := withConfig (fun c => { c with etaStruct := .none }) do
  withConfig (fun c => { c with etaStruct := .none }) do
  let constInfo ← getConstInfo matchDeclName
  let us := constInfo.levelParams.map mkLevelParam
  let some matchInfo ← getMatcherInfo? matchDeclName | throwError "`{matchDeclName}` is not a matcher function"
  let numDiscrEqs := matchInfo.getNumDiscrEqs
  forallTelescopeReducing constInfo.type fun xs _matchResultType => do
    let mut eqnNames := #[]
    let params := xs[*...matchInfo.numParams]
    let motive := xs[matchInfo.getMotivePos]!
    let alts   := xs[(xs.size - matchInfo.numAlts)...*]
    let firstDiscrIdx := matchInfo.numParams + 1
    let discrs := xs[firstDiscrIdx...(firstDiscrIdx + matchInfo.numDiscrs)]
    let mut notAlts := #[]
    let mut idx := 1
    for i in *...alts.size do
      let altNumParams := matchInfo.altNumParams[i]!
      let thmName := (Name.str baseName congrEqnThmSuffixBase).appendIndexAfter idx
      eqnNames := eqnNames.push thmName
      let notAlt ← do
        let alt := alts[i]!
        Match.forallAltVarsTelescope (← inferType alt) altNumParams numDiscrEqs fun altVars args _mask altResultType => do
        let patterns ← forallTelescope altResultType fun _ t => pure t.getAppArgs
        let mut heqsTypes := #[]
        assert! patterns.size == discrs.size
        for discr in discrs, pattern in patterns do
          let heqType ← mkEqHEq discr pattern
          heqsTypes := heqsTypes.push ((`heq).appendIndexAfter (heqsTypes.size + 1), heqType)
        withLocalDeclsDND heqsTypes fun heqs => do
          let rhs ← Match.mkAppDiscrEqs (mkAppN alt args) heqs numDiscrEqs
          let mut hs := #[]
          for overlappedBy in matchInfo.overlaps.overlapping i do
            let notAlt := notAlts[overlappedBy]!
            let h ← instantiateForall notAlt patterns
            if let some h ← simpH? h patterns.size then
              hs := hs.push h
          trace[Meta.Match.matchEqs] "hs: {hs}"
          let mut notAlt := mkConst ``False
          for discr in discrs.toArray.reverse, pattern in patterns.reverse do
            notAlt ← mkArrow (← mkEqHEq discr pattern) notAlt
          notAlt ← mkForallFVars (discrs ++ altVars) notAlt
          let lhs := mkAppN (mkConst constInfo.name us) (params ++ #[motive] ++ discrs ++ alts)
          let thmType ← mkHEq lhs rhs
          let thmType ← hs.foldrM (init := thmType) (mkArrow · ·)
          let thmType ← mkForallFVars (params ++ #[motive] ++ discrs ++ alts ++ altVars ++ heqs) thmType
          let thmType ← Match.unfoldNamedPattern thmType
          -- Here we prove the theorem from scratch. One could likely also use the (non-generalized)
          -- match equation theorem after subst'ing the `heqs`.
          let thmVal ← Match.proveCondEqThm matchDeclName thmType
            (heqPos := params.size + 1 + discrs.size + alts.size + altVars.size) (heqNum := heqs.size)
          unless (← getEnv).contains thmName do
            addDecl <| Declaration.thmDecl {
              name        := thmName
              levelParams := constInfo.levelParams
              type        := thmType
              value       := thmVal
            }
          return notAlt
      notAlts := notAlts.push notAlt
      idx := idx + 1
    registerMatchCongrEqns matchDeclName eqnNames

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
    let _ ← MetaM.run' <| genMatchCongrEqns p
  else
    let _ ← MetaM.run' <| getEquationsFor p
  return true

end Lean.Meta.Match
