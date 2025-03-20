/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Expr
import Lean.Util.MonadCache

namespace Lean
/-!
`forEachWhere p f e` is similar to `forEach f e`, but only applies `f` to subterms that satisfy the
(pure) predicate `p`.
It also uses the caching trick used at `FindExpr` and `ReplaceExpr`. This can be very effective
if the number of subterms satisfying `p` is a small subset of the set of subterms.
If `p` holds for most subterms, then it is more efficient to use `forEach f e`.
-/

namespace ForEachExprWhere
abbrev cacheSize : USize := 8192 - 1

structure State where
  /--
  Implements caching trick similar to the one used at `FindExpr` and `ReplaceExpr`.
  -/
  visited : Array Expr   -- Remark: our "unsafe" implementation relies on the fact that `()` is not a valid Expr
  /--
  Set of visited subterms that satisfy the predicate `p`.
  We have to use this set to make sure `f` is applied at most once of each subterm that satisfies `p`.
  -/
  checked : Std.HashSet Expr

unsafe def initCache : State := {
  visited := .replicate cacheSize.toNat (cast lcProof ())
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
  `e.forEachWhere p f` applies `f` to each subterm that satisfies `p`.
  If `stopWhenVisited` is `true`, the function doesn't visit subterms of terms
  which satisfy `p`.
-/
@[implemented_by ForEachExprWhere.visit]
opaque Expr.forEachWhere {ω : Type} {m : Type → Type} [STWorld ω m] [MonadLiftT (ST ω) m] [Monad m] (p : Expr → Bool) (f : Expr → m Unit) (e : Expr) (stopWhenVisited : Bool := false) : m Unit

end Lean
