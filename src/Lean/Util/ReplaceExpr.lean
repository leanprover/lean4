/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Expr

namespace Lean
namespace Expr

namespace ReplaceImpl

@[inline] def cacheSize : USize := 8192

structure Cache where
  -- First cacheSize elements are the keys.
  -- Second cacheSize elements are the results.
  keysResults : Array NonScalar -- Either Expr or Unit (disjoint memory representation)

set_option compiler.extract_closed false in
unsafe def Cache.new : Cache :=
  { keysResults := mkArray (2 * cacheSize).toNat (unsafeCast ()) }

@[inline]
unsafe def Cache.keyIdx (key : Expr) : USize :=
  (ptrAddrUnsafe key >>> 4) % cacheSize

@[inline]
unsafe def Cache.resultIdx (key : Expr) : USize :=
  keyIdx key + cacheSize

@[inline]
unsafe def Cache.hasResultFor (c : Cache) (key : Expr) : Bool :=
  have : (keyIdx key).toNat < c.keysResults.size := lcProof
  ptrEq (unsafeCast key) c.keysResults[keyIdx key]

@[inline]
unsafe def Cache.getResultFor (c : Cache) (key : Expr) : Expr :=
  have : (resultIdx key).toNat < c.keysResults.size := lcProof
  unsafeCast c.keysResults[resultIdx key]

@[inline]
unsafe def Cache.store (c : Cache) (key result : Expr) : Cache :=
  Cache.mk <| c.keysResults
    |>.uset (keyIdx key) (unsafeCast key) lcProof
    |>.uset (resultIdx key) (unsafeCast result) lcProof

abbrev ReplaceM := StateM Cache

@[inline]
unsafe def cache (key : Expr) (result : Expr) : ReplaceM Expr := do
  modify (·.store key result)
  pure result

@[specialize]
unsafe def replaceUnsafeM (f? : Expr → Option Expr) (e : Expr) : ReplaceM Expr := do
  let rec @[specialize] visit (e : Expr) := do
    if (← get).hasResultFor e then
      return (← get).getResultFor e
    else match f? e with
      | some eNew => cache e eNew
      | none      => match e with
        | Expr.forallE _ d b _   => cache e <| e.updateForallE! (← visit d) (← visit b)
        | Expr.lam _ d b _       => cache e <| e.updateLambdaE! (← visit d) (← visit b)
        | Expr.mdata _ b         => cache e <| e.updateMData! (← visit b)
        | Expr.letE _ t v b _    => cache e <| e.updateLet! (← visit t) (← visit v) (← visit b)
        | Expr.app f a           => cache e <| e.updateApp! (← visit f) (← visit a)
        | Expr.proj _ _ b        => cache e <| e.updateProj! (← visit b)
        | e                      => pure e
  visit e

@[inline]
unsafe def replaceUnsafe (f? : Expr → Option Expr) (e : Expr) : Expr :=
  (replaceUnsafeM f? e).run' Cache.new

end ReplaceImpl

/- TODO: use withPtrAddr, withPtrEq to avoid unsafe tricks above.
   We also need an invariant at `State` and proofs for the `uget` operations. -/

@[implemented_by ReplaceImpl.replaceUnsafe]
partial def replace (f? : Expr → Option Expr) (e : Expr) : Expr :=
  /- This is a reference implementation for the unsafe one above -/
  match f? e with
  | some eNew => eNew
  | none      => match e with
    | Expr.forallE _ d b _   => let d := replace f? d; let b := replace f? b; e.updateForallE! d b
    | Expr.lam _ d b _       => let d := replace f? d; let b := replace f? b; e.updateLambdaE! d b
    | Expr.mdata _ b         => let b := replace f? b; e.updateMData! b
    | Expr.letE _ t v b _    => let t := replace f? t; let v := replace f? v; let b := replace f? b; e.updateLet! t v b
    | Expr.app f a           => let f := replace f? f; let a := replace f? a; e.updateApp! f a
    | Expr.proj _ _ b        => let b := replace f? b; e.updateProj! b
    | e                      => e
end Expr

end Lean
