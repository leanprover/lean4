/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Gladshtein, Sebastian Graf
-/
module

prelude
public import Lean.Meta.Sym
public import Std.WP

open Lean Meta Sym
open Std.WP Lean.Order

namespace Lean.Elab.Tactic.VCGen


/-!
Helpers for decomposing exception-postcondition goals. An exception postcondition is a tuple with
one component per exception layer, so the head layer of `pre ⊑ epost.fst` is a `Prod.fst`
projection. `mkExceptPostAtIndex` and `peelExceptPostSndChain` select the component of a concrete
tuple. `mkExceptPostBotRule` handles the `⊥` case. Its rule turns `pre ⊑ (⊥ : _ × _).fst x₁ … xₙ`
into `pre ⊑ ⊥`.
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

/--
The backward rule `pre ⊑ ⊥ → pre ⊑ (⊥ : eh × et).fst x₁ … xₙ` for the shape of `rhs`, the right-hand
side of the entailment `target`. The exception postcondition `⊥` is propositionally—but not
definitionally—equal to the component the goal projects, so the rule carries the equation
`Prod.fst_bot` and `Lean.Order.bot_apply` establish, lifted through `pre ⊑ ·`.

`eh`, `et` and the `⊥` stay concrete; the precondition and the excess arguments become schematic, so
the rule serves every precondition and state chain of this shape. Returns `none` when the projection
does not reduce, for instance because the `⊥` carries a lattice instance the two lemmas do not match.
-/
public def mkExceptPostBotRule (target rhs : Expr) : SymM (Option BackwardRule) := do
  let relArgs := target.getAppArgs
  let args := rhs.getAppArgs
  if relArgs.size < 2 || args.size < 3 then return none
  let carrier := relArgs[0]!
  let inst := relArgs[1]!
  let vars ← (args.extract 3 args.size).mapM fun a => do mkFreshExprMVar (← Meta.inferType a)
  let rhs' := mkAppN rhs.getAppFn (args.extract 0 3 ++ vars)
  let mut thms : Sym.Simp.Theorems := {}
  for declName in [``Prod.fst_bot, ``Lean.Order.bot_apply] do
    thms := thms.insert (← Sym.Simp.mkTheoremFromDecl declName)
  let .step bot eqProof _ _ ← Sym.simp rhs' { post := thms.rewrite } | return none
  -- `h : pre ⊑ ⊥` is the rule's only subgoal; the equation `rhs' = ⊥` turns it into `pre ⊑ rhs'`.
  let pre ← mkFreshExprMVar carrier
  let relPre := mkApp3 target.getAppFn carrier inst pre
  let h ← mkFreshExprMVar (mkApp relPre bot)
  let eqMp ← mkAppM ``Eq.mp #[← mkEqSymm (← mkCongrArg relPre eqProof)]
  let res ← abstractMVars (mkApp eqMp h)
  return some (← mkBackwardRuleFromExpr res.expr res.paramNames.toList)


end Lean.Elab.Tactic.VCGen
