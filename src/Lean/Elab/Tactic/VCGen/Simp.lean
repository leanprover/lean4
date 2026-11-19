/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Lean.Elab.Tactic.VCGen.Context
public import Lean.Meta.Sym.Simp.Goal
import Lean.Meta.Sym.Simp.Result

/-!
`vcgen` simplifies terms and goals only through `runSimp`. For example, with the hypothesis
`h : s = 3` in `Scope.substs`, `runSimp scope Sym.Simp.simp (s < 5)` first rewrites `s < 5` to
`3 < 5` and then simplifies `3 < 5` to `True` with the `vcgen` simp set.
-/

open Lean Meta Sym

namespace Lean.Elab.Tactic.VCGen

/-- Rewrite a local `x` to `t` with the hypothesis `h : x = t` of `scope.substs`. -/
def eqsSimproc (scope : Scope) : Sym.Simp.Simproc := fun e => do
  let .fvar x := e | return .rfl
  let some (t, h) := scope.substs.get? x | return .rfl
  return .step t (mkFVar h) (contextDependent := true)

/-- Run `k` with `methods` on the persistent simp state `State.simpState`. -/
def runCachedSimp (methods : Sym.Simp.Methods) (k : Sym.Simp.SimpM α) : VCGenM α := do
  let st ← modifyGet fun s => (s.simpState, { s with simpState := {} })
  let (a, st) ← Sym.Simp.SimpM.run k methods (← read).simpConfig st
  modify fun s => { s with simpState := st }
  return a

/--
Simplify `e` with `k`, which selects the parts of `e` to visit: first rewrite with `scope.substs` on
empty caches, then simplify with `Context.simpMethods` on the persistent cache. The rewrite cannot
use the persistent cache, because it holds the terms with a local `x` unrewritten.
-/
public def runSimp (scope : Scope) (k : Expr → Sym.Simp.SimpM Sym.Simp.Result) (e : Expr) :
    VCGenM Sym.Simp.Result := do
  let r ← if scope.substs.isEmpty || !e.hasAnyFVar scope.substs.contains then pure .rfl
    else Sym.Simp.SimpM.run' (k e) { pre := eqsSimproc scope } (← read).simpConfig
  let some methods := (← read).simpMethods | return r
  match r with
  | .rfl .. => runCachedSimp methods (k e)
  | .step e' h .. => Sym.Simp.mkEqTransResult e e' h (← runCachedSimp methods (k e'))

/-- Simplify the target of `goal` with `runSimp scope k`. -/
public def simpGoalWith (scope : Scope) (k : Expr → Sym.Simp.SimpM Sym.Simp.Result)
    (goal : MVarId) : VCGenM Sym.SimpGoalResult := goal.withContext do
  (← runSimp scope k (← goal.getType)).toSimpGoalResult goal

end Lean.Elab.Tactic.VCGen
