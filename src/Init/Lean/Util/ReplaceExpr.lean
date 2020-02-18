/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Expr

namespace Lean
namespace Expr

namespace ReplaceImpl

abbrev cacheSize : USize := 8192

structure State :=
(keys    : Array Expr)
(used    : Array Bool)
(results : Array Expr)

abbrev ReplaceM := StateM State

@[inline] unsafe def cache (i : USize) (key : Expr) (result : Expr) : ReplaceM Expr := do
modify $ fun s => { keys := s.keys.uset i key lcProof, used := s.used.uset i true lcProof, results := s.results.uset i result lcProof };
pure result

@[specialize] unsafe def replaceUnsafeM (f? : Expr → Option Expr) (size : USize) : Expr → ReplaceM Expr
| e => do
  c ← get;
  let h := ptrAddrUnsafe e;
  let i := h % size;
  if c.used.uget i lcProof && ptrAddrUnsafe (c.keys.uget i lcProof) == h then
    pure $ c.results.uget i lcProof
  else match f? e with
    | some eNew => cache i e eNew
    | none      => match e with
      | Expr.forallE _ d b _   => do d ← replaceUnsafeM d; b ← replaceUnsafeM b; cache i e $ e.updateForallE! d b
      | Expr.lam _ d b _       => do d ← replaceUnsafeM d; b ← replaceUnsafeM b; cache i e $ e.updateLambdaE! d b
      | Expr.mdata _ b _       => do b ← replaceUnsafeM b; cache i e $ e.updateMData! b
      | Expr.letE _ t v b _    => do t ← replaceUnsafeM t; v ← replaceUnsafeM v; b ← replaceUnsafeM b; cache i e $ e.updateLet! t v b
      | Expr.app f a _         => do f ← replaceUnsafeM f; a ← replaceUnsafeM a; cache i e $ e.updateApp! f a
      | Expr.proj _ _ b _      => do b ← replaceUnsafeM b; cache i e $ e.updateProj! b
      | Expr.localE _ _ _ _    => unreachable!
      | e                      => pure e

def initCache : State :=
{ keys    := mkArray cacheSize.toNat (arbitrary _),
  results := mkArray cacheSize.toNat (arbitrary _),
  used    := mkArray cacheSize.toNat false }

@[inline] unsafe def replaceUnsafe (f? : Expr → Option Expr) (e : Expr) : Expr :=
(replaceUnsafeM f? cacheSize e).run' initCache

end ReplaceImpl

/- TODO: use withPtrAddr, withPtrEq to avoid unsafe tricks above.
   We also need an invariant at `State` and proofs for the `uget` operations. -/

@[implementedBy ReplaceImpl.replaceUnsafe]
partial def replace (f? : Expr → Option Expr) : Expr → Expr
| e =>
  /- This is a reference implementation for the unsafe one above -/
  match f? e with
  | some eNew => eNew
  | none      => match e with
    | Expr.forallE _ d b _   => let d := replace d; let b := replace b; e.updateForallE! d b
    | Expr.lam _ d b _       => let d := replace d; let b := replace b; e.updateLambdaE! d b
    | Expr.mdata _ b _       => let b := replace b; e.updateMData! b
    | Expr.letE _ t v b _    => let t := replace t; let v := replace v; let b := replace b; e.updateLet! t v b
    | Expr.app f a _         => let f := replace f; let a := replace a; e.updateApp! f a
    | Expr.proj _ _ b _      => let b := replace b; e.updateProj! b
    | e                      => e
end Expr

end Lean
