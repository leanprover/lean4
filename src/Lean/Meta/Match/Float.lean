/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

prelude
import Init.Simproc
import Lean.ResolveName
import Lean.ReservedNameAction
import Lean.Meta.Match.MatcherInfo
import Lean.Meta.Match.MatcherApp.Basic
import Lean.Meta.Match.MatchEqsExt
import Lean.Meta.AppBuilder
import Lean.Meta.Tactic.Util
import Lean.Meta.Tactic.Simp.Simproc
import Lean.Elab.SyntheticMVars
import Lean.AddDecl

open Lean Meta Elab Term

namespace Lean.Meta

-- partial def mkEquationsFor (matchDeclName : Name) :  MetaM

def deriveMatchFloat (name : Name) : MetaM Unit := do
  mapError (f := (m!"Cannot construct match floating theorem:{indentD ·}")) do
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
   Lean.registerTraceClass `match_float

private def _root_.Lean.Expr.constLams? : Expr → Option Expr
  | .lam _ _ b _ => constLams? b
  | e => if e.hasLooseBVars then none else some e

def mkMatchFloatApp (f : Expr) (matcherApp : MatcherApp) : MetaM (Option Expr) := do
  let some (α, β) := (← inferType f).arrow? |
    trace[match_float] "Cannot float match: {f} is dependent"
    return none
  let floatName := matcherApp.matcherName ++ `float
  let _ ← realizeGlobalName floatName
  let floatArgs := #[α,β,f] ++ matcherApp.params ++ matcherApp.discrs ++ matcherApp.alts
  -- Using mkAppOptM to instantiate the level params
  let e ← mkAppOptM floatName (floatArgs.map some)
  return some e

open Lean Meta Simp
builtin_simproc_decl match_float (_) := fun e => do
  unless e.isApp do return .continue
  -- We could, but for now we do not float out of props
  if ← Meta.isProp e then return .continue
  e.withApp fun fn args => do
    for h : i in [:args.size] do
      let some matcherApp ← matchMatcherApp? args[i] | continue
      -- We do not handle over-application of matches
      unless matcherApp.remaining.isEmpty do continue
      -- We do not handle dependent motives
      let some α := matcherApp.motive.constLams? |
        trace[match_float] "Cannot float match: extra arguments after the match"
        continue
      let f := (mkLambda `x .default α (mkAppN fn (args.set! i (.bvar 0)))).eta
      -- Abstracting over the argument can result in a type incorrect `f`:
      unless (← isTypeCorrect f) do
        trace[match_float] "Cannot float match: context is not type correct"
        continue
      let some proof ← mkMatchFloatApp f matcherApp | continue
      let type ← inferType proof
      let some (_, _, rhs) := type.eq?
        | throwError "match_float: Unexpected non-equality type:{indentExpr type}"
      return .visit { expr := rhs, proof? := some proof }
    return .continue
