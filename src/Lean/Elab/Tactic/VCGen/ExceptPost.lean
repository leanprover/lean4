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

private builtin_initialize botMethodsRef : IO.Ref (Option Sym.Simp.Methods) ← IO.mkRef none

/--
The `Sym.simp` methods that reduce `(⊥ : eh × et).fst x₁ … xₙ` to `⊥`. The `pre` method confines the
traversal to the `Prod.fst`/`⊥` spine, so the state arguments `x₁ … xₙ` are never visited.
-/
private def botMethods : SymM Sym.Simp.Methods := do
  if let some methods ← botMethodsRef.get then return methods
  let mut thms : Sym.Simp.Theorems := {}
  for declName in [``Prod.fst_bot, ``Lean.Order.bot_apply] do
    thms := thms.insert (← Sym.Simp.mkTheoremFromDecl declName)
  let pre : Sym.Simp.Simproc := fun e => do
    let f := e.getAppFn
    return Sym.Simp.mkRflResult (done := !(f.isConstOf ``Prod.fst || f.isConstOf ``Lean.Order.bot))
  let methods : Sym.Simp.Methods := { pre, post := thms.rewrite }
  botMethodsRef.set (some methods)
  return methods

/--
When the exception postcondition is `⊥`, the RHS of a `pre ⊑ (⊥ : eh × et).fst x₁ … xₙ` goal is
propositionally—but not definitionally—equal to `⊥`. This rewrites the goal to `pre ⊑ ⊥` by
simplifying `rhs` with `Prod.fst_bot` and `Lean.Order.bot_apply`, leaving `pre` untouched.

`target` is the `pre ⊑ rhs` entailment and `rhs` its right-hand side. Returns the rewritten goal, or
`none` if `rhs` does not simplify (the caller then falls through). -/
public def replaceExceptPostFstBot? (goal : MVarId) (target rhs : Expr) :
    SymM (Option MVarId) := do
  let .step rhs' h _ _ ← Sym.simp rhs (← botMethods) | return none
  let relArgs := target.getAppArgs
  let some α := relArgs[0]? | return none
  let some inst := relArgs[1]? | return none
  let some pre := relArgs[2]? | return none
  -- `relPre := (pre ⊑ ·) : α → Prop`
  let relPre := mkApp3 target.getAppFn α inst pre
  let uα ← Sym.getLevel α
  let eqProof :=
    mkApp6 (mkConst ``congrArg [uα, .succ .zero]) α (mkSort .zero) rhs rhs' relPre h
  return some (← goal.replaceTargetEq (mkApp relPre rhs') eqProof)


end Lean.Elab.Tactic.VCGen
