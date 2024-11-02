/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

prelude
import Lean.ResolveName
import Lean.ReservedNameAction
import Lean.Meta.Match.MatcherInfo
import Lean.Meta.Match.MatcherApp.Basic
import Lean.Meta.AppBuilder
import Lean.Meta.Tactic.Util
import Lean.Elab.SyntheticMVars
import Lean.AddDecl

-- NB: This module is Lean.Meta.MatchFloat, not Lean.Meta.Match.Float
-- so that this does not become a dependency from modules that don't need it.
-- If Lean.Meta.Match would be an import-only module this could be avoided

open Lean Meta Elab Term

namespace Lean.Meta

-- partial def mkEquationsFor (matchDeclName : Name) :  MetaM

def deriveMatchFloat (name : Name) : MetaM Unit := do
  mapError (f := (m!"Cannot construct match floating theorem (please report this issue)\n{indentD ·}")) do
    let some info ← getMatcherInfo? name | throwError "getMatcherInfo? failed"
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
    let decl := Declaration.thmDecl { name := name ++ `float, levelParams, type, value }
    addDecl decl

def isMatchFloatName (env : Environment) (name : Name) : Bool :=
  if let .str p "float" := name
  then
    (getMatcherInfoCore? env p).isSome
  else
    false

builtin_initialize
  registerReservedNamePredicate isMatchFloatName

  registerReservedNameAction fun name => do
    if isMatchFloatName (← getEnv) name then
      let .str p _ := name | return false
      MetaM.run' <| deriveMatchFloat p
      return true
    return false

end Lean.Meta

 builtin_initialize
   Lean.registerTraceClass `Meta.Match.float
