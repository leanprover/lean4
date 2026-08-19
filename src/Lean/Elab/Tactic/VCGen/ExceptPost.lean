/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Gladshtein, Sebastian Graf
-/
module

prelude
public import Lean.Meta.Sym
public import Std.WP
public import Lean.Meta.Tactic.Replace

open Lean Meta Sym
open Std.WP Lean.Order

namespace Lean.Elab.Tactic.VCGen


/-!
Helpers for decomposing exception-postcondition goals. An exception postcondition is a tuple with
one component per exception layer, so the head layer of `pre ⊑ epost.fst` is a `Prod.fst`
projection. `mkExceptPostAtIndex` and `peelExceptPostSndChain` select the component of a concrete
tuple. `replaceExceptPostFstBot?` handles the `⊥` case. It rewrites `pre ⊑ (⊥ : _ × _).fst x₁ … xₙ`
to `pre ⊑ ⊥`.
-/

/-- Get the `index`-th component of an exception postcondition tuple. -/
public def mkExceptPostAtIndex (target : Expr) (index : Nat) : SymM (Option Expr) := do
  let mut curr := target
  for _ in [:index] do
    let_expr Prod.mk _ _ _ snd := curr | return none
    curr := snd
  let_expr Prod.mk _ _ fst _ := curr | return none
  return fst

/-- Peel a chain of `Prod.snd` projections. Returns the base tuple and the number of peels. -/
public partial def peelExceptPostSndChain (curr : Expr) (idx : Nat := 0) : Expr × Nat :=
  curr.consumeMData.withApp fun fn args =>
    if fn.isConstOf ``Prod.snd && args.size > 0 then
      peelExceptPostSndChain args[args.size - 1]! (idx + 1)
    else
      (curr, idx)

/-- The `CCPO` instances of the two components of a `CCPO (eh × et)` instance. -/
private def prodCCPOComponents? (inst : Expr) : Option (Expr × Expr) :=
  if inst.isAppOf ``Lean.Order.instCCPOProd then
    let args := inst.getAppArgs
    if args.size < 2 then none else some (args[args.size - 2]!, args[args.size - 1]!)
  else none

/-- The `CCPO` instance of the codomain of a `CCPO (σ → τ)` instance. -/
private def piCodomainCCPO? (inst : Expr) : Option Expr :=
  if inst.isAppOf ``Lean.Order.instCCPOPi then
    match inst.appArg! with
    | .lam _ _ body _ => if body.hasLooseBVars then none else some body
    | _ => none
  else none

/--
When the exception postcondition is `⊥`, the RHS of a `pre ⊑ (⊥ : eh × et).fst x₁ … xₙ` goal is
propositionally—but not definitionally—equal to `⊥`. This rewrites the goal to `pre ⊑ ⊥`,
constructing the equality proof from `Prod.fst_bot` (for the first projection) and
`bot_apply` (for each excess argument).

The proof term is built directly with `mkApp`/`mkConst` and instances extracted from the existing
goal, avoiding `mkAppM`/instance synthesis (which is both expensive and unable to unify `max`-of-
universe-variable instance levels in the abstract-monad setting).

`fst`/`args` come from `rhs.withApp`, where `rhs = @Prod.fst eh et ⊥ x₁ … xₙ`, and `target`
is the full `pre ⊑ rhs` entailment. Returns the rewritten goal, or `none` if `args[2]` is not `⊥`
or the lattice instances are not in the expected shape (the caller then falls through). -/
public def replaceExceptPostFstBot? (goal : MVarId) (target fst : Expr) (args : Array Expr) :
    SymM (Option MVarId) := do
  let some eh := args[0]? | return none
  let some et := args[1]? | return none
  let some epostArg := args[2]? | return none
  -- `epostArg = @bot (eh × et) botCCPOInst`
  let_expr Lean.Order.bot _ botCCPOInst := epostArg | return none
  let [u, v] := fst.constLevels! | return none
  let some (chInst, ctInst) := prodCCPOComponents? botCCPOInst | return none
  -- `p0 : (⊥ : eh × et).fst = (⊥ : eh)`
  let fstBot := mkApp3 fst eh et epostArg
  let p0 := mkApp4 (mkConst ``Prod.fst_bot [u, v]) eh et chInst ctInst
  let some (_, _, b0) := (← Sym.inferType p0).eq? | return none
  -- Fold `bot_apply` over the excess arguments: `acc : (⊥ : eh × et).fst x₁ … xᵢ = ⊥`.
  let mut acc := p0
  let mut curFst := fstBot
  let mut curBot := b0
  let mut curTy := eh
  let mut curCCPO := chInst
  for x in args.extract 3 args.size do
    let .forallE _ σ τ _ := curTy | return none
    if τ.hasLooseBVars then return none
    let uσ ← Sym.getLevel σ
    let uτ ← Sym.getLevel τ
    let some τCCPO := piCodomainCCPO? curCCPO | return none
    -- `bfa : (⊥ : σ → τ) x = (⊥ : τ)`
    let bfa := mkApp4 (mkConst ``Lean.Order.bot_apply [← decLevel uσ, ← decLevel uτ]) σ τ τCCPO x
    let some (_, _, newBot) := (← Sym.inferType bfa).eq? | return none
    -- `Eq.trans (congrFun acc x) bfa : curFst x = ⊥`
    let cf := mkApp6 (mkConst ``congrFun [uσ, uτ]) σ (.lam `x σ τ .default) curFst curBot acc x
    acc := mkApp6 (mkConst ``Eq.trans [uτ]) τ (mkApp curFst x) (mkApp curBot x) newBot cf bfa
    curFst := mkApp curFst x
    curBot := newBot
    curTy := τ
    curCCPO := τCCPO
  -- `acc : rhs = ⊥`; lift through `pre ⊑ ·` and replace the target.
  let relArgs := target.getAppArgs
  let some α := relArgs[0]? | return none
  let some inst := relArgs[1]? | return none
  let some pre := relArgs[2]? | return none
  let relPre := mkApp3 target.getAppFn α inst pre
  let uα ← Sym.getLevel α
  let eqProof :=
    mkApp6 (mkConst ``congrArg [uα, .succ .zero]) α (mkSort .zero) (mkAppN fst args) curBot relPre acc
  return some (← goal.replaceTargetEq (mkApp relPre curBot) eqProof)


end Lean.Elab.Tactic.VCGen
