/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Expr

namespace Lean
namespace Expr

namespace ReplaceImpl

abbrev cacheSize : USize := 8192

structure State where
  keys    : Array Expr -- Remark: our "unsafe" implementation relies on the fact that `()` is not a valid Expr
  results : Array Expr

abbrev ReplaceM := StateM State

@[inline] unsafe def cache (i : USize) (key : Expr) (result : Expr) : ReplaceM Expr := do
  modify fun ⟨keys, results⟩ => { keys := keys.uset i key lcProof, results := results.uset i result lcProof };
  pure result

@[inline] unsafe def replaceUnsafeM (f? : Expr → Option Expr) (size : USize) (e : Expr) : ReplaceM Expr := do
  let rec @[specialize] visit (e : Expr) := do
    let c ← get
    let h := ptrAddrUnsafe e
    let i := h % size
    if ptrAddrUnsafe (c.keys.uget i lcProof) == h then
      pure <| c.results.uget i lcProof
    else match f? e with
      | some eNew => cache i e eNew
      | none      => match e with
        | Expr.forallE _ d b _   => cache i e <| e.updateForallE! (← visit d) (← visit b)
        | Expr.lam _ d b _       => cache i e <| e.updateLambdaE! (← visit d) (← visit b)
        | Expr.mdata _ b _       => cache i e <| e.updateMData! (← visit b)
        | Expr.letE _ t v b _    => cache i e <| e.updateLet! (← visit t) (← visit v) (← visit b)
        | Expr.app f a _         => cache i e <| e.updateApp! (← visit f) (← visit a)
        | Expr.proj _ _ b _      => cache i e <| e.updateProj! (← visit b)
        | e                      => pure e
  visit e

unsafe def initCache : State :=
  { keys    := mkArray cacheSize.toNat (cast lcProof ()), -- `()` is not a valid `Expr`
    results := mkArray cacheSize.toNat arbitrary }

@[inline] unsafe def replaceUnsafe (f? : Expr → Option Expr) (e : Expr) : Expr :=
  (replaceUnsafeM f? cacheSize e).run' initCache

end ReplaceImpl

/- TODO: use withPtrAddr, withPtrEq to avoid unsafe tricks above.
   We also need an invariant at `State` and proofs for the `uget` operations. -/

@[implementedBy ReplaceImpl.replaceUnsafe]
partial def replace (f? : Expr → Option Expr) (e : Expr) : Expr :=
  /- This is a reference implementation for the unsafe one above -/
  match f? e with
  | some eNew => eNew
  | none      => match e with
    | Expr.forallE _ d b _   => let d := replace f? d; let b := replace f? b; e.updateForallE! d b
    | Expr.lam _ d b _       => let d := replace f? d; let b := replace f? b; e.updateLambdaE! d b
    | Expr.mdata _ b _       => let b := replace f? b; e.updateMData! b
    | Expr.letE _ t v b _    => let t := replace f? t; let v := replace f? v; let b := replace f? b; e.updateLet! t v b
    | Expr.app f a _         => let f := replace f? f; let a := replace f? a; e.updateApp! f a
    | Expr.proj _ _ b _      => let b := replace f? b; e.updateProj! b
    | e                      => e
end Expr

end Lean
