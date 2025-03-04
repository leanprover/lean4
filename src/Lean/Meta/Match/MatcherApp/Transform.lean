/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Joachim Breitner
-/

prelude
import Lean.Meta.Match
import Lean.Meta.InferType
import Lean.Meta.Check
import Lean.Meta.Tactic.Split

namespace Lean.Meta.MatcherApp

/-- Auxiliary function for MatcherApp.addArg -/
private partial def updateAlts (unrefinedArgType : Expr) (typeNew : Expr) (altNumParams : Array Nat) (alts : Array Expr) (refined : Bool) (i : Nat) : MetaM (Array Nat × Array Expr) := do
  if h : i < alts.size then
    let alt       := alts[i]
    let numParams := altNumParams[i]!
    let typeNew ← whnfD typeNew
    match typeNew with
    | Expr.forallE _ d b _ =>
      let (alt, refined) ← forallBoundedTelescope d (some numParams) fun xs d => do
        let alt ← try instantiateLambda alt xs catch _ => throwError "unexpected matcher application, insufficient number of parameters in alternative"
        forallBoundedTelescope d (some 1) fun x _ => do
          let alt ← mkLambdaFVars x alt -- x is the new argument we are adding to the alternative
          let refined ← if refined then
            pure refined
          else
            pure <| !(← isDefEq unrefinedArgType (← inferType x[0]!))
          return (← mkLambdaFVars xs alt, refined)
      updateAlts unrefinedArgType (b.instantiate1 alt) (altNumParams.set! i (numParams+1)) (alts.set i alt) refined (i+1)
    | _ => throwError "unexpected type at MatcherApp.addArg"
  else
    if refined then
      return (altNumParams, alts)
    else
      throwError "failed to add argument to matcher application, argument type was not refined by `casesOn`"

/--
Given
- matcherApp `match_i As (fun xs => motive[xs]) discrs (fun ys_1 => (alt_1 : motive (C_1[ys_1])) ... (fun ys_n => (alt_n : motive (C_n[ys_n]) remaining`, and
- expression `e : B[discrs]`,
Construct the term
`match_i As (fun xs => B[xs] -> motive[xs]) discrs (fun ys_1 (y : B[C_1[ys_1]]) => alt_1) ... (fun ys_n (y : B[C_n[ys_n]]) => alt_n) e remaining`.

We only abstract discriminants that are fvars.  We used to use `kabstract` to abstract all
discriminants from `B[discrs]`, but that changes the type of the arg in ways that make it no
longer compatible with the original recursive function (issue #7322).

If this is still not great, then we could try to use `kabstract`, but only on the last paramter
of the `arg` (the termination proof obligation).

This method assumes
- the `matcherApp.motive` is a lambda abstraction where `xs.size == discrs.size`
- each alternative is a lambda abstraction where `ys_i.size == matcherApp.altNumParams[i]`

This is used in `Lean.Elab.PreDefinition.WF.Fix` when replacing recursive calls with calls to
the argument provided by `fix` to refine type of the local variable used for recursive calls,
which may mention `major`. See there for how to use this function.
-/
def addArg (matcherApp : MatcherApp) (e : Expr) : MetaM MatcherApp :=
  lambdaTelescope matcherApp.motive fun motiveArgs motiveBody => do
    unless motiveArgs.size == matcherApp.discrs.size do
      -- This error can only happen if someone implemented a transformation that rewrites the motive created by `mkMatcher`.
      throwError "unexpected matcher application, motive must be lambda expression with #{matcherApp.discrs.size} arguments"
    let eType ← inferType e
    let eTypeAbst := matcherApp.discrs.size.foldRev (init := eType) fun i _ eTypeAbst =>
      let discr     := matcherApp.discrs[i]
      if discr.isFVar then
        let motiveArg := motiveArgs[i]!
        eTypeAbst.replaceFVar discr motiveArg
      else
        eTypeAbst
    let motiveBody ← mkArrow eTypeAbst motiveBody
    let matcherLevels ← match matcherApp.uElimPos? with
      | none     => pure matcherApp.matcherLevels
      | some pos =>
        let uElim ← getLevel motiveBody
        pure <| matcherApp.matcherLevels.set! pos uElim
    let motive ← mkLambdaFVars motiveArgs motiveBody
    -- Construct `aux` `match_i As (fun xs => B[xs] → motive[xs]) discrs`, and infer its type `auxType`.
    -- We use `auxType` to infer the type `B[C_i[ys_i]]` of the new argument in each alternative.
    let aux := mkAppN (mkConst matcherApp.matcherName matcherLevels.toList) matcherApp.params
    let aux := mkApp aux motive
    let aux := mkAppN aux matcherApp.discrs
    unless (← isTypeCorrect aux) do
      throwError "failed to add argument to matcher application, type error when constructing the new motive"
    let auxType ← inferType aux
    let (altNumParams, alts) ← updateAlts eType auxType matcherApp.altNumParams matcherApp.alts false 0
    return { matcherApp with
      matcherLevels := matcherLevels,
      motive        := motive,
      alts          := alts,
      altNumParams  := altNumParams,
      remaining     := #[e] ++ matcherApp.remaining
    }

/-- Similar to `MatcherApp.addArg`, but returns `none` on failure. -/
def addArg? (matcherApp : MatcherApp) (e : Expr) : MetaM (Option MatcherApp) :=
  try
    return some (← matcherApp.addArg e)
  catch _ =>
    return none


/-- Given
  - matcherApp `match_i As (fun xs => motive[xs]) discrs (fun ys_1 => (alt_1 : motive (C_1[ys_1])) ... (fun ys_n => (alt_n : motive (C_n[ys_n]) remaining`, and
  - a expression `B[discrs]` (which may not be a type, e.g. `n : Nat`),
  returns the expressions `fun ys_1 ... ys_i => B[C_1[ys_1]] ... B[C_n[ys_n]]`,

  This method assumes
  - the `matcherApp.motive` is a lambda abstraction where `xs.size == discrs.size`
  - each alternative is a lambda abstraction where `ys_i.size == matcherApp.altNumParams[i]`

  This is similar to `MatcherApp.addArg` when you only have an expression to
  refined, and not a type with a value.

  This is used in `Lean.Elab.PreDefinition.WF.GuessFix` when constructing the context of recursive
  calls to refine the functions' parameter, which may mention `major`.
  See there for how to use this function.
-/
def refineThrough (matcherApp : MatcherApp) (e : Expr) : MetaM (Array Expr) :=
  lambdaTelescope matcherApp.motive fun motiveArgs _motiveBody => do
    unless motiveArgs.size == matcherApp.discrs.size do
      -- This error can only happen if someone implemented a transformation that rewrites the motive created by `mkMatcher`.
      throwError "failed to transfer argument through matcher application, motive must be lambda expression with #{matcherApp.discrs.size} arguments"

    let eAbst ← matcherApp.discrs.size.foldRevM (init := e) fun i _ eAbst => do
      let motiveArg := motiveArgs[i]!
      let discr     := matcherApp.discrs[i]
      let eTypeAbst ← kabstract eAbst discr
      return eTypeAbst.instantiate1 motiveArg
    -- Let's create something that’s a `Sort` and mentions `e`
    -- (recall that `e` itself possibly isn't a type),
    -- by writing `e = e`, so that we can use it as a motive
    let eEq ← mkEq eAbst eAbst

    let matcherLevels ← match matcherApp.uElimPos? with
      | none     => pure matcherApp.matcherLevels
      | some pos =>
        pure <| matcherApp.matcherLevels.set! pos levelZero
    let motive ← mkLambdaFVars motiveArgs eEq
    let aux := mkAppN (mkConst matcherApp.matcherName matcherLevels.toList) matcherApp.params
    let aux := mkApp aux motive
    let aux := mkAppN aux matcherApp.discrs
    unless (← isTypeCorrect aux) do
      throwError "failed to transfer argument through matcher application, type error when constructing the new motive"
    let auxType ← inferType aux
    forallTelescope auxType fun altAuxs _ => do
      let altAuxTys ← altAuxs.mapM (inferType ·)
      (Array.zip matcherApp.altNumParams altAuxTys).mapM fun (altNumParams, altAuxTy) => do
        forallBoundedTelescope altAuxTy altNumParams fun fvs body => do
          unless fvs.size = altNumParams do
            throwError "failed to transfer argument through matcher application, alt type must be telescope with #{altNumParams} arguments"
          -- extract type from our synthetic equality
          let body := body.getArg! 2
          -- and abstract over the parameters of the alternatives, so that we can safely pass the Expr out
          mkLambdaFVars fvs body

/-- A non-failing version of `MatcherApp.refineThrough` -/
def refineThrough? (matcherApp : MatcherApp) (e : Expr) :
    MetaM (Option (Array Expr)) :=
  try
    return some (← matcherApp.refineThrough e)
  catch _ =>
    return none


private def withUserNamesImpl {α} (fvars : Array Expr) (names : Array Name) (k : MetaM α) : MetaM α := do
  let lctx := (Array.zip fvars names).foldl (init := ← (getLCtx)) fun lctx (fvar, name) =>
    lctx.setUserName fvar.fvarId! name
  withLCtx' lctx k

/--
Sets the user name of the FVars in the local context according to the given array of names.

If they differ in size the shorter size wins.
-/
def withUserNames {n} [MonadControlT MetaM n] [Monad n]
  {α} (fvars : Array Expr) (names : Array Name) (k : n α) : n α := do
  mapMetaM (withUserNamesImpl fvars names) k

/-
`Match.forallAltTelescope` lifted to a monad transformer
(and only passing those arguments that we care about below)
-/
private def forallAltTelescope'
    {n} [Monad n] [MonadControlT MetaM n]
    {α} (origAltType : Expr) (numParams numDiscrEqs : Nat)
    (k : Array Expr → Array Expr → n α) : n α := do
  map2MetaM (fun k =>
    Match.forallAltTelescope origAltType (numParams - numDiscrEqs) 0
      fun ys _eqs args _mask _bodyType => k ys args
  ) k

/--
Performs a possibly type-changing transformation to a `MatcherApp`.

* `onParams` is run on each parameter and discriminant
* `onMotive` runs on the body of the motive, and is passed the motive parameters
  (one for each `MatcherApp.discrs`)
* `onAlt` runs on each alternative, and is passed the expected type of the alternative,
   as inferred from the motive
* `onRemaining` runs on the remaining arguments (and may change their number)

If `useSplitter` is true, the matcher is replaced with the splitter.
NB: Not all operations on `MatcherApp` can handle one `matcherName` is a splitter.

If `addEqualities` is true, then equalities connecting the discriminant to the parameters of the
alternative (like in `match h : x with …`) are be added, if not already there.

This function works even if the type of alternatives do *not* fit the inferred type. This
allows you to post-process the `MatcherApp` with `MatcherApp.inferMatchType`, which will
infer a type, given all the alternatives.
-/
def transform
    {n} [MonadLiftT MetaM n] [MonadControlT MetaM n] [Monad n] [MonadError n] [MonadEnv n] [MonadLog n]
    [AddMessageContext n] [MonadOptions n]
    (matcherApp : MatcherApp)
    (useSplitter := false)
    (addEqualities : Bool := false)
    (onParams : Expr → n Expr := pure)
    (onMotive : Array Expr → Expr → n Expr := fun _ e => pure e)
    (onAlt : Expr → Expr → n Expr := fun _ e => pure e)
    (onRemaining : Array Expr → n (Array Expr) := pure) :
    n MatcherApp := do

  -- We also handle CasesOn applications here, and need to treat them specially in a
  -- few places.
  -- TODO: Expand MatcherApp with the necessary fields to make this more uniform
  -- (in particular, include discrEq and whether there is a splitter)
  let isCasesOn := isCasesOnRecursor (← getEnv) matcherApp.matcherName

  let numDiscrEqs ←
    if isCasesOn then pure 0 else
    match ← getMatcherInfo? matcherApp.matcherName with
    | some info => pure info.getNumDiscrEqs
    | none      => throwError "matcher {matcherApp.matcherName} has no MatchInfo found"

  let params' ← matcherApp.params.mapM onParams
  let discrs' ← matcherApp.discrs.mapM onParams

  let (motive', uElim, addHEqualities) ← lambdaTelescope matcherApp.motive fun motiveArgs motiveBody => do
    unless motiveArgs.size == matcherApp.discrs.size do
      throwError "unexpected matcher application, motive must be lambda expression with #{matcherApp.discrs.size} arguments"
    let mut motiveBody' ← onMotive motiveArgs motiveBody

    -- Prepend `(x = e) →` or `(HEq x e) → ` to the motive when an equality is requested
    -- and not already present, and remember whether we added an Eq or a HEq
    let mut addHEqualities : Array (Option Bool) := #[]
    for arg in motiveArgs, discr in discrs', di in matcherApp.discrInfos do
      if addEqualities && di.hName?.isNone then
        if ← isProof arg then
          addHEqualities := addHEqualities.push none
        else
          let heq ← mkEqHEq discr arg
          motiveBody' ← liftMetaM <| mkArrow heq motiveBody'
          addHEqualities := addHEqualities.push heq.isHEq
      else
        addHEqualities := addHEqualities.push none

    return (← mkLambdaFVars motiveArgs motiveBody', ← getLevel motiveBody', addHEqualities)

  let matcherLevels ← match matcherApp.uElimPos? with
    | none     => pure matcherApp.matcherLevels
    | some pos => pure <| matcherApp.matcherLevels.set! pos uElim

  -- We pass `Eq.refl`s for all the equations we added as extra arguments
  -- (and count them along the way)
  let mut remaining' := #[]
  let mut extraEqualities : Nat := 0
  for discr in discrs'.reverse, b in addHEqualities.reverse do
    match b with
    | none => pure ()
    | some is_heq =>
        remaining' := remaining'.push (← (if is_heq then mkHEqRefl else mkEqRefl) discr)
        extraEqualities := extraEqualities + 1

  if useSplitter && !isCasesOn then
    let aux1 := mkAppN (mkConst matcherApp.matcherName matcherLevels.toList) params'
    let aux1 := mkApp aux1 motive'
    let aux1 := mkAppN aux1 discrs'
    unless (← isTypeCorrect aux1) do
      logError m!"failed to transform matcher, type error when constructing new pre-splitter motive:{indentExpr aux1}"
      check aux1
    let origAltTypes ← inferArgumentTypesN matcherApp.alts.size aux1

    -- We replace the matcher with the splitter
    let matchEqns ← Match.getEquationsFor matcherApp.matcherName
    let splitter := matchEqns.splitterName

    let aux2 := mkAppN (mkConst splitter matcherLevels.toList) params'
    let aux2 := mkApp aux2 motive'
    let aux2 := mkAppN aux2 discrs'
    unless (← isTypeCorrect aux2) do
      logError m!"failed to transform matcher, type error when constructing splitter motive:{indentExpr aux2}"
      check aux2
    let altTypes ← inferArgumentTypesN matcherApp.alts.size aux2

    let mut alts' := #[]
    for alt in matcherApp.alts,
        numParams in matcherApp.altNumParams,
        splitterNumParams in matchEqns.splitterAltNumParams,
        origAltType in origAltTypes,
        altType in altTypes do
      let alt' ← forallAltTelescope' origAltType (numParams - numDiscrEqs) 0 fun ys args => do
        let altType ← instantiateForall altType ys
        -- The splitter inserts its extra parameters after the first ys.size parameters, before
        -- the parameters for the numDiscrEqs
        forallBoundedTelescope altType (splitterNumParams - ys.size) fun ys2 altType => do
          forallBoundedTelescope altType numDiscrEqs fun ys3 altType => do
            forallBoundedTelescope altType extraEqualities fun ys4 altType => do
              let alt ← try instantiateLambda alt (args ++ ys3)
                        catch _ => throwError "unexpected matcher application, insufficient number of parameters in alternative"
              let alt' ← onAlt altType alt
              mkLambdaFVars (ys ++ ys2 ++ ys3 ++ ys4) alt'
      alts' := alts'.push alt'

    remaining' := remaining' ++ (← onRemaining matcherApp.remaining)

    return { matcherApp with
      matcherName   := splitter
      matcherLevels := matcherLevels
      params        := params'
      motive        := motive'
      discrs        := discrs'
      altNumParams  := matchEqns.splitterAltNumParams.map (· + extraEqualities)
      alts          := alts'
      remaining     := remaining'
    }
  else
    let aux := mkAppN (mkConst matcherApp.matcherName matcherLevels.toList) params'
    let aux := mkApp aux motive'
    let aux := mkAppN aux discrs'
    unless (← isTypeCorrect aux) do
      logError m!"failed to transform matcher, type error when constructing new motive:{indentExpr aux}"
      check aux
    let altTypes ← inferArgumentTypesN matcherApp.alts.size aux

    let mut alts' := #[]
    for alt in matcherApp.alts,
        numParams in matcherApp.altNumParams,
        altType in altTypes do
      let alt' ← forallBoundedTelescope altType numParams fun xs altType => do
        forallBoundedTelescope altType extraEqualities fun ys4 altType => do
          -- we should try to preserve the variable names in the alternative
          let names ← lambdaTelescope alt fun xs _ => xs.mapM (·.fvarId!.getUserName)
          withUserNames xs names do
            let alt ← instantiateLambda alt xs
            let alt' ← onAlt altType alt
            mkLambdaFVars (xs ++ ys4) alt'
      alts' := alts'.push alt'

    remaining' := remaining' ++ (← onRemaining matcherApp.remaining)

    return { matcherApp with
      matcherLevels := matcherLevels
      params        := params'
      motive        := motive'
      discrs        := discrs'
      altNumParams  := matcherApp.altNumParams.map (· + extraEqualities)
      alts          := alts'
      remaining     := remaining'
    }



/--
Given a `MatcherApp`, replaces the motive with one that is inferred from the actual types of the
alternatives.

For example, given
```
(match (motive := Nat → Unit → ?) n with
 0 => 1
 _ => true) ()
```
(for any `?`; the motive’s result type be ignored) will give this type
```
(match n with
 | 0 => Nat
 | _ => Bool)
```

The given `MatcherApp` must not use a splitter in `matcherName`.
The resulting expression *will* use the splitter corresponding to `matcherName` (this is necessary
for the construction).

Internally, this needs to reduce the matcher in a given branch; this is done using
`Split.simpMatchTarget`.
-/
def inferMatchType (matcherApp : MatcherApp) : MetaM MatcherApp := do
  -- In matcherApp.motive, replace the (dummy) matcher body with a type
  -- derived from the inferred types of the alternatives
  let nExtra := matcherApp.remaining.size
  matcherApp.transform (useSplitter := true)
    (onMotive := fun motiveArgs body => do
      let extraParams ← arrowDomainsN nExtra body
      let propMotive ← mkLambdaFVars motiveArgs (.sort levelZero)
      let propAlts ← matcherApp.alts.mapM fun termAlt =>
        lambdaTelescope termAlt fun xs termAltBody => do
          -- We have alt parameters and parameters corresponding to the extra args
          let xs1 := xs[0 : xs.size - nExtra]
          let xs2 := xs[xs.size - nExtra : xs.size]
          -- logInfo m!"altIH: {xs} => {altIH}"
          let altType ← inferType termAltBody
          for x in xs2 do
            if altType.hasAnyFVar (· == x.fvarId!) then
              throwError "Type {altType} of alternative {termAlt} still depends on {x}"
          -- logInfo m!"altIH type: {altType}"
          mkLambdaFVars xs1 altType
      let matcherLevels ← match matcherApp.uElimPos? with
        | none     => pure matcherApp.matcherLevels
        | some pos => pure <| matcherApp.matcherLevels.set! pos levelOne
      let typeMatcherApp := { matcherApp with
        motive := propMotive
        matcherLevels := matcherLevels
        discrs := motiveArgs
        alts := propAlts
        remaining := #[]
      }
      mkArrowN extraParams typeMatcherApp.toExpr
    )
    (onAlt := fun expAltType alt => do
      let altType ← inferType alt
      let eq ← mkEq expAltType altType
      let proof ← mkFreshExprSyntheticOpaqueMVar eq
      let goal := proof.mvarId!
      -- logInfo m!"Goal: {goal}"
      let goal ← Split.simpMatchTarget goal
      -- logInfo m!"Goal after splitting: {goal}"
      try
        goal.refl
      catch _ =>
        logInfo m!"Cannot close goal after splitting: {goal}"
        goal.admit
      mkEqMPR proof alt
    )

end Lean.Meta.MatcherApp
