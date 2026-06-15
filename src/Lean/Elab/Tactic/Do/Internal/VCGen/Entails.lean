/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf, Vladimir Gladshtein
-/
module

prelude
public import Lean.Elab.Tactic.Do.Internal.VCGen.Context
public import Lean.Elab.Tactic.Do.Internal.VCGen.EPost
public import Lean.Elab.Tactic.Do.Internal.VCGen.RuleCache
public import Lean.Elab.Tactic.Do.Internal.VCGen.Util
public import Lean.Meta.Sym.Util
import Lean.Meta.Sym.InferType

open Lean Meta Elab Tactic Sym Sym.Internal
open Lean.Elab.Tactic.Do.Internal.SpecAttr
open Lean.Elab.Tactic.Do.Internal
open Std.Internal.Do Lean.Order

/-!
Entailment-shaped goal decomposition for `pre ⊑ rhs` targets: unfolding `Triple`,
introducing excess state arguments and pure preconditions, reducing
exception-postcondition projections, and decomposing lattice connectives.
-/

namespace Lean.Elab.Tactic.Do.Internal

namespace VCGen

/-- Unfold `⦃P⦄ x ⦃Q; E⦄` into the underlying entailment `P ⊑ wp x Q E`. -/
public def unfoldTriple (goal : MVarId) : VCGenM MVarId := do
  let .goals [goal] ← (← read).introRules.tripleIntro.applyChecked goal
    | throwError "Failed to unfold the Triple target of {goal}"
  return goal

/-- Apply precondition-intro rule `rule` to `goal`, then introduce the freed hypothesis,
leaving `⊤` as the residual precondition. Returns the new goal and the introduced hypothesis. -/
public def introPre (rule : BackwardRule) (goal : MVarId) : VCGenM (MVarId × FVarId) := do
  let .goals [goal] ← rule.applyChecked goal
    | throwError "Failed to apply precondition intro rule to {goal}"
  let goal ← introsHygienic goal
  let some decl := (← goal.withContext getLCtx).lastDecl
    | throwError "Failed to intro the lifted precondition of {goal}"
  return (goal, decl.fvarId)

/--
Reduce an `EPost.Cons.head` projection on the RHS of `pre ⊑ rhs` to the underlying component:
concrete `epost⟨…⟩` values project to the selected component, and `⊥.head x₁ … xₙ` rewrites to
`⊥` via `replaceEPostHeadBot?`. Returns `none` if the RHS is not such a projection.
-/
public def reduceEPostHead? (goal : MVarId) (target α inst pre rhs : Expr) :
    VCGenM (Option MVarId) :=
  rhs.withApp fun head args => do
    unless head.isConstOf ``EPost.Cons.head do return none
    let some epostArg := args[2]? | return none
    -- `⊥.head x₁ … xₙ` is propositionally `⊥`; reduce it to a clean `pre ⊑ ⊥` VC.
    if epostArg.isAppOf ``Lean.Order.bot then
      return (← replaceEPostHeadBot? goal target head args)
    let (epostTarget, index) := peelEPostTailChain epostArg
    let some epost ← mkEPostAtIndex epostTarget index | return none
    let excessArgs := args.drop 3
    let rhs ← betaS epost excessArgs
    let newTarget ← mkAppNS target.getAppFn #[α, inst, pre, rhs]
    return some (← goal.replaceTargetDefEq newTarget)

/--
Decompose a supported lattice connective (`⊓`, `⇨`, `⌜p⌝`, `⊤`) on the RHS of `pre ⊑ rhs` by
applying the corresponding cached logic rule. Returns `none` if the RHS head is not a supported
connective.

An embedded proposition `⌜p⌝` is only decomposed when the precondition is `⊤`: turning
`pre ⊑ ⌜p⌝` into the subgoal `p` drops `pre`, which can make the goal unprovable otherwise.
-/
public def solveLatticeConnective? (goal : MVarId) (target rhs : Expr) :
    VCGenM (Option (List MVarId)) :=
  rhs.withApp fun head args => do
    let applyLattice (c : LatticeSplit) (as excessArgs : Array Expr)
        (resultType? : Option Expr := none) : VCGenM (List MVarId) := do
      let rule ← mkBackwardRuleForLatticeCached c as excessArgs resultType?
      let .goals goals ← rule.applyChecked goal
        | throwError "Failed to apply lattice rule at {indentExpr target}"
      return goals
    match_expr head with
    | meet =>
      return some (← applyLattice .meet (args.extract 2 4) (args.drop 4))
    | himp =>
      return some (← applyLattice .himp (args.extract 2 4) (args.drop 4))
    | CompleteLattice.ofProp =>
      let preIsTop := match target.app4? ``Lean.Order.PartialOrder.rel with
        | some (_, _, pre, _) => pre.isAppOf ``Lean.Order.top && pre.getAppNumArgs == 2
        | none => false
      unless preIsTop do return none
      return some (← applyLattice .ofProp (args.extract 2 3) (args.drop 3) args[0]!)
    | top =>
      return some (← applyLattice .top #[] (args.drop 2) args[0]!)
    | _ => return none

/-- Reduce a `Prop`-lattice goal `(⊤ : Prop) ⊑ φ` to the bare proposition `φ` via `top_le_prop`,
returning any other goal unchanged. The match on `Sort 0` keeps it to the `Prop` base lattice,
where the reduction is sound; entailments at an abstract lattice carrier pass through. -/
public def elimTopPre (goal : MVarId) : VCGenM MVarId := do
  let some (.sort .zero, _, pre, _) := (← goal.getType).app4? ``Lean.Order.PartialOrder.rel
    | return goal
  unless pre.isAppOf ``Lean.Order.top do return goal
  let .goals [goal] ← (← read).elimPreRule.apply goal
    | throwError "Failed to strip the `⊤ ⊑` wrapper of {goal}"
  return goal

end VCGen

end Lean.Elab.Tactic.Do.Internal
