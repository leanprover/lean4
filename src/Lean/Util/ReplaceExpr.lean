/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Gabriel Ebner, Sebastian Ullrich
-/
import Lean.Expr

namespace Lean
namespace Expr

namespace ReplaceImpl

structure Cache where
  size : USize
  -- First `size` elements are the keys.
  -- Second `size` elements are the results.
  keysResults : Array NonScalar -- Either Expr or Unit (disjoint memory representation)

unsafe def Cache.new (e : Expr) : Cache :=
  -- scale size with approximate number of subterms up to 8k
  -- make sure size is coprime with power of two for collision avoidance
  let size := (1 <<< min (max e.approxDepth.toUSize 1) 13) - 1
  { size, keysResults := mkArray (2 * size).toNat (unsafeCast ()) }

@[inline]
unsafe def Cache.keyIdx (c : Cache) (key : Expr) : USize :=
  ptrAddrUnsafe key % c.size

@[inline]
unsafe def Cache.resultIdx (c : Cache) (key : Expr) : USize :=
  c.keyIdx key + c.size

@[inline]
unsafe def Cache.hasResultFor (c : Cache) (key : Expr) : Bool :=
  have : (c.keyIdx key).toNat < c.keysResults.size := lcProof
  ptrEq (unsafeCast key) c.keysResults[c.keyIdx key]

@[inline]
unsafe def Cache.getResultFor (c : Cache) (key : Expr) : Expr :=
  have : (c.resultIdx key).toNat < c.keysResults.size := lcProof
  unsafeCast c.keysResults[c.resultIdx key]

unsafe def Cache.store (c : Cache) (key result : Expr) : Cache :=
  { c with keysResults := c.keysResults
    |>.uset (c.keyIdx key) (unsafeCast key) lcProof
    |>.uset (c.resultIdx key) (unsafeCast result) lcProof }

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
  (replaceUnsafeM f? e).run' (Cache.new e)

end ReplaceImpl

/- TODO: use withPtrAddr, withPtrEq to avoid unsafe tricks above.
   We also need an invariant at `State` and proofs for the `uget` operations. -/

@[specialize]
def replaceNoCache (f? : Expr → Option Expr) (e : Expr) : Expr :=
  match f? e with
  | some eNew => eNew
  | none      => match e with
    | .forallE _ d b _ => let d := replaceNoCache f? d; let b := replaceNoCache f? b; e.updateForallE! d b
    | .lam _ d b _     => let d := replaceNoCache f? d; let b := replaceNoCache f? b; e.updateLambdaE! d b
    | .mdata _ b       => let b := replaceNoCache f? b; e.updateMData! b
    | .letE _ t v b _  => let t := replaceNoCache f? t; let v := replaceNoCache f? v; let b := replaceNoCache f? b; e.updateLet! t v b
    | .app f a         => let f := replaceNoCache f? f; let a := replaceNoCache f? a; e.updateApp! f a
    | .proj _ _ b      => let b := replaceNoCache f? b; e.updateProj! b
    | e                => e

@[implemented_by ReplaceImpl.replaceUnsafe]
partial def replace (f? : Expr → Option Expr) (e : Expr) : Expr :=
  e.replaceNoCache f?
