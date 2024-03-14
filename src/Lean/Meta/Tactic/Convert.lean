/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean.Meta.Tactic.Congr!

/-!
# The `convert` tactic.
-/

open Lean Meta Elab Tactic

/--
Close the goal `g` using `Eq.mp v e`,
where `v` is a metavariable asserting that the type of `g` and `e` are equal.
Then call `MVarId.congrN!` (also using local hypotheses and reflexivity) on `v`,
and return the resulting goals.

With `sym = true`, reverses the equality in `v`, and uses `Eq.mpr v e` instead.
With `depth = some n`, calls `MVarId.congrN! n` instead, with `n` as the max recursion depth.
-/
def Lean.MVarId.convert (e : Expr) (sym : Bool)
    (depth : Option Nat := none) (config : Congr!.Config := {})
    (patterns : List (TSyntax `rcasesPat) := []) (g : MVarId) :
    MetaM (List MVarId) := do
  let src ← inferType e
  let tgt ← g.getType
  let v ← mkFreshExprMVar (← mkAppM ``Eq (if sym then #[src, tgt] else #[tgt, src]))
  g.assign (← mkAppM (if sym then ``Eq.mp else ``Eq.mpr) #[v, e])
  let m := v.mvarId!
  m.congrN! depth config patterns
