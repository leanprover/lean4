/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Gladshtein, Sebastian Graf
-/
module

prelude
public import Lean.Meta.Sym
public import Std.Internal.Do
public import Lean.Meta.Tactic.Replace

open Lean Meta Sym
open Std.Internal.Do Lean.Order

namespace Lean.Elab.Tactic.Do.Internal

namespace VCGen

/-!
Helpers for decomposing exception-postcondition (`EPost`) goals: reducing an `EPost.Cons.head`
projection in the RHS of an entailment to the underlying component. The concrete case
(`epost⟨…⟩`) is handled by `mkEPostAtIndex`/`peelEPostTailChain`; the `⊥` case is handled by
`replaceEPostHeadBot?`, which rewrites `pre ⊑ ⊥.head x₁ … xₙ` to `pre ⊑ ⊥`.
-/

/-- Get the `index`-th component from an `EPost` target. -/
public def mkEPostAtIndex (target : Expr) (index : Nat) : SymM (Option Expr) := do
  let mut curr := target
  for _ in [:index] do
    let_expr EPost.Cons.mk _ _ _ tail := curr | return none
    curr := tail
  let_expr EPost.Cons.mk _ _ head _ := curr | return none
  return head

/-- Peel a chain of `.tail` projections, returning the base `EPost` and the number of tails. -/
public partial def peelEPostTailChain (curr : Expr) (idx : Nat := 0) : Expr × Nat :=
  curr.consumeMData.withApp fun fn args =>
    if fn.isConstOf ``EPost.Cons.tail && args.size > 0 then
      peelEPostTailChain args[args.size - 1]! (idx + 1)
    else
      (curr, idx)

/--
When the exception postcondition is `⊥`, the RHS of a `pre ⊑ EPost.Cons.head ⊥ x₁ … xₙ` goal is
propositionally—but not definitionally—equal to `⊥`. This rewrites the goal to `pre ⊑ ⊥`,
constructing the equality proof from `EPost.Cons.head_bot` (for the head projection) and
`bot_apply` (for each excess argument).

The proof term is built directly with `mkApp`/`mkConst` and instances extracted from the existing
goal, avoiding `mkAppM`/instance synthesis (which is both expensive and unable to unify `max`-of-
universe-variable instance levels in the abstract-monad setting).

`head`/`args` come from `rhs.withApp`, where `rhs = EPost.Cons.head eh et ⊥ x₁ … xₙ`, and `target`
is the full `pre ⊑ rhs` entailment. Returns the rewritten goal, or `none` if `args[2]` is not `⊥`
or the lattice instances are not in the expected shape (the caller then falls through). -/
public def replaceEPostHeadBot? (goal : MVarId) (target head : Expr) (args : Array Expr) :
    SymM (Option MVarId) := do
  let some eh := args[0]? | return none
  let some et := args[1]? | return none
  let some epostArg := args[2]? | return none
  -- `epostArg = @bot (EPost.Cons eh et) (scopedCCPO (instCompleteLattice eh et chInst ctInst))`
  let_expr Lean.Order.bot _ botCCPOInst := epostArg | return none
  unless botCCPOInst.isApp do return none
  let clArgs := botCCPOInst.appArg!.getAppArgs
  unless clArgs.size ≥ 2 do return none
  let chInst := clArgs[clArgs.size - 2]!
  let ctInst := clArgs[clArgs.size - 1]!
  let [u, v] := head.constLevels! | return none
  -- `p0 : EPost.Cons.head ⊥ = (⊥ : eh)`
  let headBot := mkApp3 head eh et epostArg
  let p0 := mkApp4 (mkConst ``EPost.Cons.head_bot [u, v]) eh et chInst ctInst
  let some (_, _, b0) := (← Sym.inferType p0).eq? | return none
  -- Fold `bot_apply` over the excess arguments: `acc : EPost.Cons.head ⊥ x₁ … xᵢ = ⊥`.
  let mut acc := p0
  let mut curHead := headBot
  let mut curBot := b0
  let mut curTy := eh
  let mut curCL := chInst
  for x in args.extract 3 args.size do
    let .forallE _ σ τ _ := curTy | return none
    if τ.hasLooseBVars then return none
    unless curCL.isAppOf ``Lean.Order.instCompleteLatticePi do return none
    let .lam _ _ τCL _ := curCL.appArg! | return none
    let uσ ← Sym.getLevel σ
    let uτ ← Sym.getLevel τ
    -- `bfa : (⊥ : σ → τ) x = (⊥ : τ)`
    let bfa := mkApp4 (mkConst ``Lean.Order.bot_apply [← decLevel uσ, ← decLevel uτ]) σ τ τCL x
    let some (_, _, newBot) := (← Sym.inferType bfa).eq? | return none
    -- `Eq.trans (congrFun acc x) bfa : curHead x = ⊥`
    let cf := mkApp6 (mkConst ``congrFun [uσ, uτ]) σ (.lam `x σ τ .default) curHead curBot acc x
    acc := mkApp6 (mkConst ``Eq.trans [uτ]) τ (mkApp curHead x) (mkApp curBot x) newBot cf bfa
    curHead := mkApp curHead x
    curBot := newBot
    curTy := τ
    curCL := τCL
  -- `acc : rhs = ⊥`; lift through `pre ⊑ ·` and replace the target.
  let relArgs := target.getAppArgs
  let some α := relArgs[0]? | return none
  let some inst := relArgs[1]? | return none
  let some pre := relArgs[2]? | return none
  let relPre := mkApp3 target.getAppFn α inst pre
  let uα ← Sym.getLevel α
  let eqProof :=
    mkApp6 (mkConst ``congrArg [uα, .succ .zero]) α (mkSort .zero) (mkAppN head args) curBot relPre acc
  return some (← goal.replaceTargetEq (mkApp relPre curBot) eqProof)

end VCGen

end Lean.Elab.Tactic.Do.Internal
