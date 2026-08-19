/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Lean.Elab.Tactic.VCGen.Util
public import Lean.Meta.Sym.InstantiateS
import Lean.Meta.Sym.InstantiateMVarsS
import Lean.Meta.BinderNameHint

open Lean Meta Sym

namespace Lean.Elab.Tactic.VCGen

/-!
A `@[spec]` theorem states a `binderNameHint` where the program names a value, and `vcgen` reads
the name from it when it introduces the binder that stands for that value.
-/

/-- The binder names of the matcher a state lambda applies to its own argument:
`fun x => match x with | (lo, hi) => …` carries `lo` and `hi`. -/
private def stateMatcherAltNames? (f : Expr) : VCGenM (Option (Array Name)) := do
  let .lam _ _ body _ := f.headBeta.cleanupAnnotations | return none
  let .const c _ := body.getAppFn | return none
  let some info := Meta.getMatcherInfoCore? (← getEnv) c | return none
  unless info.numDiscrs == 1 && info.getNumDiscrEqs == 0 do return none
  let some numParams := info.altNumParams[0]? | return none
  unless info.altNumParams.all (· == numParams) do return none
  let args := body.getAppArgs
  unless args.size == info.arity do return none
  unless args[info.getFirstDiscrPos]!.cleanupAnnotations == .bvar 0 do return none
  let mut alt := args[info.getFirstAltPos]!
  let mut names := #[]
  for _ in *...numParams do
    let .lam n _ b _ := alt | return none
    names := names.push n
    alt := b
  return some names

/-- The names a hint's binder argument carries: `fun acc => …` carries `acc`, and the state lambda
of `inv pref suff` carries the names of the matcher it applies to its argument. -/
private def hintNames (binder : Expr) : VCGenM (Array Name) := do
  let mut binder := binder.cleanupAnnotations
  unless binder.isLambda do
    binder := (← instantiateMVarsIfMVarAppS binder).cleanupAnnotations
  if let .lam n _ _ _ := binder then
    if isProgramName n then return #[n]
  return (← stateMatcherAltNames? binder).getD #[]

/-- The components of the right-nested tuple `e`: `(a, b, c)` has `#[a, b, c]`. -/
private partial def tupleLeaves (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  match_expr e with
  | Prod.mk _ _ a b => tupleLeaves b (acc.push a)
  | _ => acc.push e

/-- Rename the variables a chain of `binderNameHint`s at the head of `e` names, and return the
innermost payload. A hinted `(lo, hi)` names one variable per component. The first hint wins: a
variable that already carries an accessible name keeps it. -/
public partial def consumeBinderNameHintCore (goal : MVarId) (e : Expr) :
    VCGenM (Option (MVarId × Expr)) := do
  unless e.getAppFn.isConstOf ``binderNameHint do return none
  let n := e.getAppNumArgs
  unless n ≥ 6 do return none
  let leaves := tupleLeaves (e.getArg! 3 n)
  let names ← hintNames (e.getArg! 4 n)
  let mut goal := goal
  if names.size == leaves.size then
    for leaf in leaves, name in names do
      let .fvar fvarId := leaf | continue
      if (← fvarId.getDecl).userName.hasMacroScopes && isProgramName name then
        trace[Elab.Tactic.Do.vcgen] "binder-name-hint: rename {Expr.fvar fvarId} to {name}"
        goal ← liftMetaM <| goal.rename fvarId name
  -- An over-applied hint leaves the payload applied to the excess arguments, such as the state a
  -- lifted postcondition takes after its result.
  let payload := e.getArg! 5 n
  let stripped ← if n == 6 then pure payload else betaRevS payload (e.getAppArgs.extract 6 n).reverse
  return some ((← consumeBinderNameHintCore goal stripped).getD (goal, stripped))

/-- `consumeBinderNameHintCore` at the target's own head. -/
public def consumeBinderNameHint? (goal : MVarId) (target : Expr) : VCGenM (Option MVarId) := do
  let some (goal, stripped) ← consumeBinderNameHintCore goal target | return none
  return some (← goal.replaceTargetDefEqFast stripped)

/-- Erase the hints a verification condition still carries, such as one that frame-rule unification
embedded under a wand, so the discharging tactic sees every atom bare. -/
public def _root_.Lean.Meta.Grind.Goal.eraseBinderNameHints (goal : Grind.Goal) :
    VCGenM Grind.Goal := do
  let target ← goal.mvarId.getType
  unless target.hasBinderNameHint do return goal
  let target ← shareCommon (← liftMetaM <| Expr.resolveBinderNameHint target)
  return { goal with mvarId := ← goal.mvarId.replaceTargetDefEqFast target }

end Lean.Elab.Tactic.VCGen
