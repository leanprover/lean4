/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

prelude
import Lean.Meta.Match.MatcherApp.Basic
import Lean.Meta.Match.MatchEqsExt
import Lean.Elab.Tactic.Meta

open Lean Meta Elab Term

namespace Lean.Meta

def deriveMatchLift (name : Name) : MetaM Unit := do
  mapError (f := (m!"Cannot construct match lifter:{indentD ·}")) do
    let some info ← getMatcherInfo? name | throwError "getMatcherInfo? failed"
    -- Fail early if splitter cannot be generated
    try
      discard <| Match.getEquationsFor name
    catch _ =>
      throwError "Could not construct splitter for {name}"

    let cinfo ← getConstInfo name
    let (u, v, us, us', levelParams) := if let some upos := info.uElimPos? then
      let u := mkLevelParam `u
      let v := mkLevelParam `v
      let lps := (List.range cinfo.levelParams.length).map (Name.mkSimple s!"u_{·+1}")
      let us := lps.map mkLevelParam
      let us := us.set upos u
      let us' := us.set upos v
      let lps := [`u, `v] ++ lps.eraseIdx upos
      (u, v, us, us', lps)
    else
      let lps := cinfo.levelParams
      let us := lps.map mkLevelParam
      (0, 0, us, us, lps)
    let matchf := .const name us
    let matchType ← inferType matchf
    let type ← forallBoundedTelescope matchType info.numParams fun params matchType => do
      let matchType ← whnf matchType
      unless matchType.isForall do throwError "resual type {matchType} of {.ofConstName name} not a forall"
      withLocalDecl `α .implicit (.sort u) fun α => do
      withLocalDecl `β .implicit (.sort v) fun β => do
      withLocalDeclD `f (← mkArrow α β) fun f => do
        let motive ← forallTelescope matchType.bindingDomain! fun xs _ => mkLambdaFVars xs α
        let motive' ← forallTelescope matchType.bindingDomain! fun xs _ => mkLambdaFVars xs β
        let matchType ← instantiateForall matchType #[motive]
        forallBoundedTelescope matchType info.numDiscrs fun discrs matchType => do
        forallBoundedTelescope matchType info.altNumParams.size fun alts _ => do
          let lhs := mkAppN (.const name us) (params ++ #[motive] ++ discrs ++ alts)
          let lhs := .app f lhs
          let alts' ← alts.mapM fun alt => do
            let altType ← inferType alt
            forallTelescope altType fun ys _ =>
              if ys.size == 1 && altType.bindingDomain!.isConstOf ``Unit then
                mkLambdaFVars ys (mkApp f (mkApp alt (.const ``Unit.unit [])))
              else
                mkLambdaFVars ys (mkApp f (mkAppN alt ys))
          let rhs := mkAppN (.const name us') (params ++ #[motive'] ++ discrs ++ alts')
          let type ← mkEq lhs rhs
          mkForallFVars (#[α,β,f] ++ params ++ discrs ++ alts) type
    let value ← mkFreshExprSyntheticOpaqueMVar type
    TermElabM.run' do withoutErrToSorry do
      runTactic value.mvarId! (← `(Parser.Term.byTactic| by intros; split <;> rfl)).raw .term
    let value ← instantiateMVars value
    let decl := Declaration.thmDecl { name := name ++ `lifter, levelParams, type, value }
    addDecl decl

def isMatchLiftName (env : Environment) (name : Name) : Bool :=
  if let .str p "lifter" := name
  then
    (getMatcherInfoCore? env p).isSome
  else
    false

def mkMatchLifterApp (f : Expr) (matcherApp : MatcherApp) : MetaM (Option Expr) := do
  let some (α, β) := (← inferType f).arrow? |
    trace[lift_match] "Cannot lift match: {f} is dependent"
    return none
  let lifterName := matcherApp.matcherName ++ `lifter
  let _ ← realizeGlobalName lifterName
  let lifterArgs := #[α,β,f] ++ matcherApp.params ++ matcherApp.discrs ++ matcherApp.alts
  -- using mkAppOptM to instantiate the level params
  let e ← mkAppOptM lifterName (lifterArgs.map some)
  return some e

builtin_initialize
  registerReservedNamePredicate isMatchLiftName

  registerReservedNameAction fun name => do
    if isMatchLiftName (← getEnv) name then
      let .str p _ := name | return false
      MetaM.run' <| deriveMatchLift p
      return true
    return false

  Lean.registerTraceClass `lift_match
