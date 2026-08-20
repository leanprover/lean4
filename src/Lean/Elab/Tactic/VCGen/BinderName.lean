/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Lean.Elab.Tactic.VCGen.Util
public import Lean.Meta.Sym.InstantiateS
public import Lean.Meta.Sym.AlphaShareBuilder
import Lean.Meta.Sym.InstantiateMVarsS
import Lean.Meta.BinderNameHint

open Lean Meta Sym Sym.Internal Lean.Order

namespace Lean.Elab.Tactic.VCGen

/-!
# Accessible names from the program

A specification theorem introduces binders, such as the `a` of a lambda `fun a => e`. `vcgen`
introduces `a` inaccessibly as `a✝`, because `tactic.hygienic` is set.

A specification can state where an accessible name comes from. It states such a lambda as
`fun a => binderNameHint a (fun acc => p) e`, where `fun acc => p` is a subexpression of the
program. `vcgen` then introduces `a` accessibly as `acc`. This module implements that step.
`binderNameHint v binder e` is the identity on `e`, so the specification states the same assertion.

`Spec.bind` states the hint over the continuation `f`:
```
Triple (x >>= f) (wp x (fun a => binderNameHint a f (wp (f a) post epost)) epost) post epost
```
For a program `let acc ← e`, the continuation `f` is `fun acc => p`. `vcgen` renames the variable it
introduced for `a` to `acc`, so the verification condition states `acc` rather than `a✝`.
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

/-- Consume the hints of the target, and of either side of `pre ⊑ rhs`. A hint of the precondition
is consumed before the precondition becomes a hypothesis. -/
public def consumeBinderNameHint? (goal : MVarId) (target : Expr) : VCGenM (Option MVarId) := do
  if let some (goal, stripped) ← consumeBinderNameHintExpr goal target then
    return some (← goal.replaceTargetDefEqFast stripped)
  let_expr PartialOrder.rel α inst pre rhs := target | return none
  let mut goal := goal
  let mut pre' := pre
  let mut rhs' := rhs
  if let some (g, stripped) ← consumeBinderNameHintExpr goal pre then
    goal := g
    -- The stripped hint exposes `inv pref suff (a, b)`; reduce it to the invariant's body.
    pre' ← reduceHead stripped
  if let some (g, stripped) ← consumeBinderNameHintExpr goal rhs then
    goal := g
    rhs' := stripped
  if isSameExpr pre pre' && isSameExpr rhs rhs' then return none
  let target ← mkAppNS target.getAppFn #[α, inst, pre', rhs']
  return some (← goal.replaceTargetDefEqFast target)

end Lean.Elab.Tactic.VCGen
