/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

prelude
import Init.Simproc
import Lean.Meta.Match.MatcherApp.Basic
import Lean.Meta.KAbstract
import Lean.Elab.Tactic.Conv.Basic

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

def mkMatchFloatApp (f : Expr) (matcherApp : MatcherApp) : MetaM (Option Expr) := do
  let some (α, β) := (← inferType f).arrow? |
    trace[float_match] "Cannot float match: {f} is dependent"
    return none
  let floatName := matcherApp.matcherName ++ `float
  let _ ← realizeGlobalName floatName
  let floatArgs := #[α,β,f] ++ matcherApp.params ++ matcherApp.discrs ++ matcherApp.alts
  -- Using mkAppOptM to instantiate the level params
  let e ← mkAppOptM floatName (floatArgs.map some)
  return some e

builtin_initialize
   Lean.registerTraceClass `float_match


/-!
The implementation support the simproc and the conv tactic
-/

section FloatMatch

private def _root_.Lean.Expr.constLams? : Expr → Option Expr
  | .lam _ _ b _ => constLams? b
  | e => if e.hasLooseBVars then none else some e

private partial def findMatchToFloat? (e : Expr) (far : Bool) (depth : Nat := 0) : MetaM (Option (Expr × MatcherApp)) := do
  if !far && depth > 1 then
    return none

  if e.isApp then
    if depth > 0 then
      if let some matcherApp ← matchMatcherApp? e then
        if matcherApp.remaining.isEmpty then
          return some (e, matcherApp)


    let args := e.getAppArgs
    if e.isAppOf ``ite then
      -- Special-handling for if-then-else:
      -- * We do not want to float out of the branches.
      -- * We want to be able to float out of
      --      @ite ([ ] = true) (instDecidableEqBool [ ] true) t e
      --   but doing it one application at a time does not work due to the dependency.
      --   So to work around this, we do not bump the depth counter here.
      if h : args.size > 1 then
        if let some r ← findMatchToFloat? args[1] far depth then
          return some r
    else
      for a in args do
        if let some r ← findMatchToFloat? a far (depth + 1) then
          return some r

  if e.isLet then
    if let some r ← findMatchToFloat? e.letValue! far (depth + 1) then
      return some r

  return none

def floatMatch (e : Expr) (far : Bool) : MetaM (Option (Expr × Expr)) := do
  unless far do
    -- In the simproc: We could, but for now we do not float out of props
    if ← Meta.isProp e then return none
  let some (me, matcherApp) ← findMatchToFloat? e far| return none
  -- We do not handle over-application of matches
  unless matcherApp.remaining.isEmpty do
    trace[float_match] "Cannot float match: extra arguments after the match"
    return none
  -- We do not handle dependent motives
  let some α := matcherApp.motive.constLams? |
    trace[float_match] "Cannot float match: motive depends on targets"
    return none
  -- Using kabstract, rather than just abstracting over the single occurrence of `me` in `e` with
  -- helps if later arguments depend on the abstracted argument,
  -- in particular with ``ite's `Decidable c` parameter
  let f := (mkLambda `x .default α (← kabstract e me)).eta
  -- Abstracting over the argument can result in a type incorrect `f` (like in `rw`)
  unless (← isTypeCorrect f) do
    trace[float_match] "Cannot float match: context is not type correct"
    return none
  let some proof ← mkMatchFloatApp f matcherApp | return none
  let type ← inferType proof
  let some (_, _, rhs) := type.eq?
    | throwError "float_match: Unexpected non-equality type:{indentExpr type}"
  return some (rhs, proof)

end FloatMatch

/-!
The simproc tactic
-/

section Simproc

/--
Floats out `match` expressions, or, equivalently, pushes function applications into the
branches of a match. For example it can rewrite
```
f (match o with | some x => x + 1 | none => 0)
```
to
```
match o with | some x => f (x + 1) | none => f 0
```

It can only float matches with a non-dependent motive, no extra arguments and when the context
(here `fun x => f x`) is type-correct and is not a proposition.

It is recommended to enable this simproc only selectively, and not by default, as it looks for
match expression to float at every step of the simplifier.

Also see the `conv`-tactic `float_match`.
-/
builtin_simproc_decl float_match (_) := fun e => do
  let some (rhs, proof) ← floatMatch (far := false) e | return .continue
  return .visit { expr := rhs, proof? := some proof }

end Simproc

end Lean.Meta

/-!
The conv tactic
-/

namespace Lean.Elab.Tactic.Conv

@[builtin_tactic Lean.Parser.Tactic.Conv.floatMatch]
def evalFloatMatch : Tactic := fun _ => do
  let mvarId ← getMainGoal
  mvarId.withContext do
    let lhs ← getLhs
    let some (rhs, proof) ← floatMatch (far := true) lhs
      | throwError "cannot find match to float"
    updateLhs rhs proof

end Lean.Elab.Tactic.Conv
