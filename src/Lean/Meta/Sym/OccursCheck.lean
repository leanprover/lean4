/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.SymM
namespace Lean.Meta.Sym

/-!
# Occurs check

`occursCheck mvarId e` is the `SymM` counterpart of `Lean.occursCheck`. It skips the subterms
without metavariables, and uses pointer equality to visit each shared subterm once. Thus, its cost
is `O(1)` for ground terms, and linear in the number of subterms of `e` containing metavariables
otherwise.

## Design note: skipping subterms using metavariable indices

We have tried to avoid the traversal using a trick similar to `maxFVar`. It is not used because it
does not pay off in practice, but we document it here in case this check becomes a bottleneck.

**The idea.** Cache, using pointer equality, a strict upper bound on the declaration index of the
metavariables occurring in each term. Assignments are ignored, so the entries never become stale,
and only terms containing metavariables need an entry. Then, when checking whether `?m` occurs in
`e`, a subterm whose bound is `≤ ?m`'s index can be skipped. In particular, the check is `O(1)`
when the bound of `e` itself is `≤ ?m`'s index. This is the common case in `Pattern.unify?`: the
metavariables created for the pattern variables are newer than the ones in the target.

**The problem.** Unlike `maxFVar`, where the local context of a metavariable bounds the free
variables of any value assigned to it, nothing bounds the metavariables in the value assigned to
a metavariable. A skipped subterm may contain an older assigned metavariable `?k` whose value
contains `?m`, and terms in `SymM` do contain assigned metavariables.

**The guard.** We say an assignment `?a := v` is *backward* if `v` contains a metavariable newer
than `?a`. Skipping is sound if `?m` was created by the current unification and no backward
assignment was performed during it: a path from a skipped subterm to `?m` must go through a
backward assignment performed after `?m` was created. Thus, the unifier has to track whether it
performed a backward assignment, and conservatively assume one whenever `Meta.isDefEq` (type
checks, instances) is used on terms containing metavariables. Note that restricting the guard to
metavariables occurring in the target is not sufficient: `?x := f ?y` followed by `?y := g ?x` is
a cycle among the metavariables created for the pattern variables.

**Why it is not used.** In the `vcgen` benchmarks, all 6024 checks on terms containing
metavariables took the `O(1)` path, but each of them visits only 2 subterms with the simple
traversal. The extra cache, the unifier state, and the soundness argument above are not justified
by this workload. The trick only helps when a metavariable created by the unifier is assigned a
big term containing unassigned metavariables.
-/

/-- Returns `true` if `mvarId` occurs in `e`. -/
partial def occursIn (mvarId : MVarId) (e : Expr) : StateRefT (Std.HashSet ExprPtr) SymM Bool := do
  if !e.hasExprMVar then
    return false
  else if let .mvar mvarId' := e then
    if mvarId' == mvarId then
      return true
    else if let some v ← getExprMVarAssignment? mvarId' then
      occursIn mvarId v
    else if let some d ← getDelayedMVarAssignment? mvarId' then
      occursIn mvarId (mkMVar d.mvarIdPending)
    else
      return false
  else if (← get).contains { expr := e } then
    return false
  else
    modify (·.insert { expr := e })
    match e with
    | .app f a => occursIn mvarId f <||> occursIn mvarId a
    | .lam _ d b _ | .forallE _ d b _ => occursIn mvarId d <||> occursIn mvarId b
    | .letE _ t v b _ => occursIn mvarId t <||> occursIn mvarId v <||> occursIn mvarId b
    | .mdata _ b | .proj _ _ b => occursIn mvarId b
    | _ => return false

/--
Returns `true` if `mvarId` does **not** occur in `e`, directly or indirectly.
This function considers assignments and delayed assignments.
-/
public def occursCheck (mvarId : MVarId) (e : Expr) : SymM Bool := do
  if !e.hasExprMVar then
    return true
  else
    return !(← occursIn mvarId e |>.run' {})

end Lean.Meta.Sym
