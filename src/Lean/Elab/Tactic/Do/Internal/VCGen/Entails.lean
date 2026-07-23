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
import Lean.Meta.Sym.InstantiateMVarsS

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
  let .goals [goal] ← (← read).backwardRules.tripleIntro.applyChecked goal
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
    return some (← goal.replaceTargetDefEqFast newTarget)

/-- Refold a meet upper adjoint `upperAdjoint (meet F) Q s⃗` on the RHS of `pre ⊑ rhs` to the Heyting
implication `(F ⇨ Q) s⃗`, rewriting `goal` and returning it with its new RHS, so it decomposes through
the clean pointwise `⇨` split instead of generic point-framing. Returns `none` if the RHS is not a
meet upper adjoint. -/
private def refoldHimpUpperAdjoint? (goal : MVarId) (rhs : Expr) :
    VCGenM (Option (MVarId × Expr)) :=
  rhs.withApp fun head args => do
    unless head.isConstOf ``Lean.Order.PreservesSup.upperAdjoint do return none
    let some slice := args[2]? | return none
    unless slice.isAppOf ``Lean.Order.meet do return none
    let some Q := args[3]? | return none
    let rhs' := mkAppN (← mkAppM ``Lean.Order.himp #[slice.appArg!, Q]) (args.extract 4 args.size)
    let target ← goal.getType
    let newTarget := mkAppN target.getAppFn (target.getAppArgs.set! 3 rhs')
    return some (← goal.replaceTargetDefEqFast newTarget, rhs')

/--
Decompose a supported lattice connective (`⊓`, `⇨`, `⌜p⌝`, `⊤`) or a registered frame operator on the
RHS of `pre ⊑ rhs` by saturating it with the built-in and `@[frameproc]` rewrites, closing it with a
terminal, and point-framing any excess state arguments. Returns `none` if the head is neither a
built-in connective nor a frame operator, or its rule does not apply.

An embedded proposition `⌜p⌝` is decomposed only when the precondition is `⊤`: its `⊤`-fixed terminal
`top_le_ofProp` fails to apply otherwise, since turning `pre ⊑ ⌜p⌝` into the subgoal `p` drops `pre`.
-/
public def splitLatticeOp? (goal : MVarId) (rhs : Expr) :
    VCGenM (Option (List MVarId)) := do
  -- Refold a meet upper adjoint to `F ⇨ Q` up front, so the dispatch below takes the clean `⇨` path.
  let (goal, rhs) := (← refoldHimpUpperAdjoint? goal rhs).getD (goal, rhs)
  let some headName := rhs.getAppFn.constName? | return none
  -- A split applies only for a built-in connective or a registered frame operator.
  let some op := (← read).latticeOps[headName]? | return none
  let rule ← mkLatticeOpRuleCached rhs op
  match ← rule.applyChecked goal with
  | .goals goals => return some goals
  | .failed => return none

/--
Reduce a precondition that is the bare top applied to the state arguments introduced by
`le_of_forall_le`, `(⊤ : σ₁ → … → σₙ → Prop) s₁ … sₙ`, to the bare `(⊤ : Prop)`, rewriting `goal`'s
target `pre ⊑ rhs` to `⊤ ⊑ rhs`. The equation `pre = ⊤` is built on demand by folding
`Lean.Order.top_apply` over the excess arguments (mirroring `replaceEPostHeadBot?`'s `bot_apply`
fold) and applied with `replaceTargetEq`.

The proof term is built directly with `mkApp`/`mkConst` and instances extracted from `pre`, avoiding
`mkAppM`/instance synthesis (both expensive and unable to unify `max`-of-universe-variable instance
levels in the abstract-monad setting). Returns `none` if `pre` is not the bare top applied to ≥ 1
argument, or its lattice instances are not in the expected `instCompleteLatticePi` shape (the caller
then falls through).
-/
public def reduceTopAppliedPre? (goal : MVarId) (target pre : Expr) : SymM (Option MVarId) := do
  unless pre.isAppOf ``Lean.Order.top && pre.getAppNumArgs > 2 do return none
  let args := pre.getAppArgs
  let some carrier := args[0]? | return none
  let some instTop := args[1]? | return none
  -- `base = @top carrier instTop`, the unapplied lifted top; `pre = base s₁ … sₙ`.
  let base := mkApp2 pre.getAppFn carrier instTop
  -- Fold `top_apply` over the excess arguments: `acc : base s₁ … sᵢ = (⊤ : …)`.
  let mut acc := mkApp2 (mkConst ``Eq.refl [← Sym.getLevel carrier]) carrier base
  let mut curTop := base   -- `base s₁ … sᵢ`, the LHS of `acc`
  let mut curBare := base  -- `(⊤ : …)`, the RHS of `acc`
  let mut curTy := carrier
  let mut curCL := instTop
  for x in args.extract 2 args.size do
    let .forallE _ σ τ _ ← instantiateMVarsIfMVarAppS curTy | return none
    if τ.hasLooseBVars then return none
    unless curCL.isAppOf ``Lean.Order.instCompleteLatticePi do return none
    let .lam _ _ τCL _ := curCL.appArg! | return none
    let uσ ← Sym.getLevel σ
    let uτ ← Sym.getLevel τ
    -- `tfa : (⊤ : σ → τ) x = (⊤ : τ)`
    let tfa := mkApp4 (mkConst ``Lean.Order.top_apply [← decLevel uσ, ← decLevel uτ]) σ τ τCL x
    let some (_, _, newBare) := (← Sym.inferType tfa).eq? | return none
    -- `cf : curTop x = curBare x` (congrFun acc x), then `acc : curTop x = newBare`.
    let cf := mkApp6 (mkConst ``congrFun [uσ, uτ]) σ (.lam `x σ τ .default) curTop curBare acc x
    acc := mkApp6 (mkConst ``Eq.trans [uτ]) τ (mkApp curTop x) (mkApp curBare x) newBare cf tfa
    curTop := mkApp curTop x
    curBare := newBare
    curTy := τ
    curCL := τCL
  -- `acc : pre = (⊤ : Prop)`; lift through `· ⊑ rhs` and replace the target.
  let relArgs := target.getAppArgs
  let some α := relArgs[0]? | return none
  let some inst := relArgs[1]? | return none
  let some rhs := relArgs[3]? | return none
  let uα ← Sym.getLevel α
  -- `f := (· ⊑ rhs) : α → Prop`
  let f := Expr.lam `p α (mkApp4 target.getAppFn α inst (.bvar 0) rhs) .default
  let eqProof := mkApp6 (mkConst ``congrArg [uα, .succ .zero]) α (mkSort .zero) pre curBare f acc
  let newTarget := mkApp4 target.getAppFn α inst curBare rhs
  return some (← goal.replaceTargetEq newTarget eqProof)

/-- Reduce a `Prop`-lattice goal `(⊤ : Prop) ⊑ φ` to the bare proposition `φ` via `top_le_prop`,
returning any other goal unchanged. The match on `Sort 0` keeps it to the `Prop` base lattice,
where the reduction is sound; entailments at an abstract lattice carrier pass through. -/
public def elimTopPre (goal : MVarId) : VCGenM MVarId := do
  let some (.sort .zero, _, pre, _) := (← goal.getType).app4? ``Lean.Order.PartialOrder.rel
    | return goal
  unless (← instantiateMVarsIfMVarAppS pre).isAppOf ``Lean.Order.top do return goal
  let .goals [goal] ← (← read).backwardRules.elimPre.apply goal
    | throwError "Failed to strip the `⊤ ⊑` wrapper of {goal}"
  return goal

end VCGen

end Lean.Elab.Tactic.Do.Internal
