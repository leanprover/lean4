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
`Spec.bind` states `binderNameHint a f …`, so the value `f` binds as `acc` reaches its verification
condition as `acc` rather than as `a✝`.
-/

/-- The binder names of the matcher a state lambda applies to its own argument:
`fun x => match x with | (lo, hi) => …` carries `lo` and `hi`. -/
private def stateMatcherAltNames? (f : Expr) : VCGenM (Array Name) := do
  let .lam _ _ body _ := f | return #[]
  let some app ← Meta.matchMatcherApp? body | return #[]
  unless app.discrs.size == 1 && app.discrs[0]!.cleanupAnnotations == .bvar 0 do return #[]
  let some alt := app.alts[0]? | return #[]
  let mut names := #[]
  let mut alt := alt
  while true do
    let .lam n _ b _ := alt | break
    names := names.push n
    alt := b
  return names

/-- The names a hint's binder argument carries: `fun acc => …` carries `acc`, and the state lambda
of `inv pref suff` carries the names of the matcher it applies to its argument. -/
private def hintNames (binder : Expr) : VCGenM (Array Name) := do
  let mut binder := binder.cleanupAnnotations
  unless binder.isLambda do
    binder := (← instantiateMVarsIfMVarAppS binder).cleanupAnnotations.headBeta
  if let .lam n _ _ _ := binder then
    if isProgramName n then return #[n]
  stateMatcherAltNames? binder

/-- The components of the right-nested tuple `e`: `(a, b, c)` has `#[a, b, c]`. -/
private partial def tupleLeaves (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  match_expr e with
  | Prod.mk _ _ a b => tupleLeaves b (acc.push a)
  | _ => acc.push e

/-- Rename the variables that the `binderNameHint`s at the head of `e` name, and return the payload
they wrap. `Spec.bind`'s `binderNameHint a f …` names one variable; `Spec.forInPure` states a chain
of four, and a hinted `(lo, hi)` names one variable per component. The first hint wins, so a
variable that already carries an accessible name keeps it. -/
private partial def consumeBinderNameHintExpr (goal : MVarId) (e : Expr) :
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
  let payload := e.getArg! 5 n
  let stripped ← if n == 6 then pure payload else betaRevS payload (e.getAppArgs.extract 6 n).reverse
  return some ((← consumeBinderNameHintExpr goal stripped).getD (goal, stripped))

/-- `consumeBinderNameHintExpr` at the target's own head. -/
public def consumeBinderNameHint? (goal : MVarId) (target : Expr) : VCGenM (Option MVarId) := do
  let some (goal, stripped) ← consumeBinderNameHintExpr goal target | return none
  return some (← goal.replaceTargetDefEqFast stripped)

/-- Consume the hints that instantiating a goal exposes at either side of `pre ⊑ rhs`. The
instantiation puts `binderNameHint pref inv …` at the head of the precondition of a loop's step,
where the entailment shapes `solve` matches on no longer apply. -/
public def consumeEntailmentHints (goal : MVarId) (pre rhs : Expr) :
    VCGenM (MVarId × Expr × Expr) := do
  let mut goal := goal
  let mut pre := pre
  let mut rhs := rhs
  if let some (g, stripped) ← consumeBinderNameHintExpr goal pre then
    goal := g
    -- The stripped hint exposes `inv pref suff (a, b)`; reduce it to the invariant's body.
    pre ← reduceHead stripped
  if let some (g, stripped) ← consumeBinderNameHintExpr goal rhs then
    goal := g
    rhs := stripped
  return (goal, pre, rhs)

/-- Erase the hints a verification condition still carries, such as one that frame-rule unification
embedded under a wand, so the discharging tactic sees every atom bare. -/
public def _root_.Lean.Meta.Grind.Goal.resolveBinderNameHint (goal : Grind.Goal) :
    VCGenM Grind.Goal := do
  let target ← goal.mvarId.getType
  unless target.hasBinderNameHint do return goal
  let target ← shareCommon (← liftMetaM <| Expr.resolveBinderNameHint target)
  return { goal with mvarId := ← goal.mvarId.replaceTargetDefEqFast target }

end Lean.Elab.Tactic.VCGen
