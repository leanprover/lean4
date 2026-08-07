/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Expr
public import Lean.Util.MonadCache

public section

namespace Lean
/-!
`forEachWhere p f e` traverses `e` like `forEach f e`, but calls `f` only on subterms satisfying the
pure predicate `p`. Matching subterms are deduplicated by structural equality, so `f` is called at
most once for each distinct matching expression even when it occurs in multiple places.

The traversal also uses the pointer cache used by `FindExpr` and `ReplaceExpr`. This can be much more
efficient than `forEach` when `p` selects a small subset of subterms or when `f` is expensive. If `p`
holds for most subterms and duplicate suppression is unnecessary, the cache and hash-set overhead can
make `forEach` faster.
-/

namespace ForEachExprWhere
abbrev cacheSize : USize := 8192 - 1

private def notAnExpr : Unit × Unit := ⟨⟨⟩, ⟨⟩⟩

structure State where
  /--
  Implements caching trick similar to the one used at `FindExpr` and `ReplaceExpr`.
  -/
  visited : Array Expr   -- Remark: our "unsafe" implementation relies on the fact that `notAnExpr` is not a valid Expr
  /--
  Set of visited subterms that satisfy the predicate `p`.
  We have to use this set to make sure `f` is applied at most once of each subterm that satisfies `p`.
  -/
  checked : Std.HashSet Expr

unsafe def initCache : State := {
  visited := .replicate cacheSize.toNat (cast lcProof notAnExpr)
  checked := {}
}

abbrev ForEachM {ω : Type} (m : Type → Type) [STWorld ω m] := StateRefT' ω State m

variable {ω : Type} {m : Type → Type} [STWorld ω m] [MonadLiftT (ST ω) m] [Monad m]

unsafe def visited (e : Expr) : ForEachM m Bool := do
  let s ← get
  let h := ptrAddrUnsafe e
  let i := h % cacheSize
  let k := s.visited.uget i lcProof
  if ptrAddrUnsafe k == h then
    return true
  else
    modify fun s => { s with visited := s.visited.uset i e lcProof }
    return false

def checked (e : Expr) : ForEachM m Bool := do
  if (← get).checked.contains e then
    return true
  else
    modify fun s => { s with checked := s.checked.insert e }
    return false

/-- `Expr.forEachWhere` (unsafe) implementation -/
unsafe def visit (p : Expr → Bool) (f : Expr → m Unit) (e : Expr) (stopWhenVisited : Bool := false) : m Unit := do
  go e |>.run' initCache
where
  go (e : Expr) : StateRefT' ω State m Unit := do
    unless (← visited e) do
      if p e then
        unless (← checked e) do
          f e
          if stopWhenVisited then
            return ()
      match e with
      | .forallE _ d b _   => go d; go b
      | .lam _ d b _       => go d; go b
      | .letE _ t v b _    => go t; go v; go b
      | .app f a           => go f; go a
      | .mdata _ b         => go b
      | .proj _ _ b        => go b
      | _                  => return ()

end ForEachExprWhere

/--
`e.forEachWhere p f` applies `f` at most once to each structurally distinct subterm of `e` that
satisfies `p`. In particular, repeated structurally equal occurrences do not cause repeated calls.

If `stopWhenVisited` is `true`, the traversal does not descend below a matching subterm when `f` is
called for that subterm.
-/
@[implemented_by ForEachExprWhere.visit]
opaque Expr.forEachWhere {ω : Type} {m : Type → Type} [STWorld ω m] [MonadLiftT (ST ω) m] [Monad m] (p : Expr → Bool) (f : Expr → m Unit) (e : Expr) (stopWhenVisited : Bool := false) : m Unit

end Lean
