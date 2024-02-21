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
    let alt       := alts.get ⟨i, h⟩
    let numParams := altNumParams[i]!
    let typeNew ← whnfD typeNew
    match typeNew with
    | Expr.forallE _ d b _ =>
      let (alt, refined) ← forallBoundedTelescope d (some numParams) fun xs d => do
        let alt ← try instantiateLambda alt xs catch _ => throwError "unexpected matcher application, insufficient number of parameters in alternative"
        forallBoundedTelescope d (some 1) fun x _ => do
          let alt ← mkLambdaFVars x alt -- x is the new argument we are adding to the alternative
          let refined := if refined then refined else
            !(← isDefEq unrefinedArgType (← inferType x[0]!))
          return (← mkLambdaFVars xs alt, refined)
      updateAlts unrefinedArgType (b.instantiate1 alt) (altNumParams.set! i (numParams+1)) (alts.set ⟨i, h⟩ alt) refined (i+1)
    | _ => throwError "unexpected type at MatcherApp.addArg"
  else
    if refined then
      return (altNumParams, alts)
    else
      throwError "failed to add argument to matcher application, argument type was not refined by `casesOn`"

/-- Given
  - matcherApp `match_i As (fun xs => motive[xs]) discrs (fun ys_1 => (alt_1 : motive (C_1[ys_1])) ... (fun ys_n => (alt_n : motive (C_n[ys_n]) remaining`, and
  - expression `e : B[discrs]`,
  Construct the term
  `match_i As (fun xs => B[xs] -> motive[xs]) discrs (fun ys_1 (y : B[C_1[ys_1]]) => alt_1) ... (fun ys_n (y : B[C_n[ys_n]]) => alt_n) e remaining`.

  We use `kabstract` to abstract the discriminants from `B[discrs]`.

  This method assumes
  - the `matcherApp.motive` is a lambda abstraction where `xs.size == discrs.size`
  - each alternative is a lambda abstraction where `ys_i.size == matcherApp.altNumParams[i]`

  This is used in in `Lean.Elab.PreDefinition.WF.Fix` when replacing recursive calls with calls to
  the argument provided by `fix` to refine the termination argument, which may mention `major`.
  See there for how to use this function.
-/
def addArg (matcherApp : MatcherApp) (e : Expr) : MetaM MatcherApp :=
  lambdaTelescope matcherApp.motive fun motiveArgs motiveBody => do
    unless motiveArgs.size == matcherApp.discrs.size do
      -- This error can only happen if someone implemented a transformation that rewrites the motive created by `mkMatcher`.
      throwError "unexpected matcher application, motive must be lambda expression with #{matcherApp.discrs.size} arguments"
    let eType ← inferType e
    let eTypeAbst ← matcherApp.discrs.size.foldRevM (init := eType) fun i eTypeAbst => do
      let motiveArg := motiveArgs[i]!
      let discr     := matcherApp.discrs[i]!
      let eTypeAbst ← kabstract eTypeAbst discr
      return eTypeAbst.instantiate1 motiveArg
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

  This is used in in `Lean.Elab.PreDefinition.WF.GuessFix` when constructing the context of recursive
  calls to refine the functions' paramter, which may mention `major`.
  See there for how to use this function.
-/
def refineThrough (matcherApp : MatcherApp) (e : Expr) : MetaM (Array Expr) :=
  lambdaTelescope matcherApp.motive fun motiveArgs _motiveBody => do
    unless motiveArgs.size == matcherApp.discrs.size do
      -- This error can only happen if someone implemented a transformation that rewrites the motive created by `mkMatcher`.
      throwError "failed to transfer argument through matcher application, motive must be lambda expression with #{matcherApp.discrs.size} arguments"

    let eAbst ← matcherApp.discrs.size.foldRevM (init := e) fun i eAbst => do
      let motiveArg := motiveArgs[i]!
      let discr     := matcherApp.discrs[i]!
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

end Lean.Meta.MatcherApp
