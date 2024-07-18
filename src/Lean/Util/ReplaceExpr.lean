/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Gabriel Ebner, Sebastian Ullrich
-/
prelude
import Lean.Expr
import Lean.Util.PtrSet

namespace Lean
namespace Expr

namespace ReplaceImpl

unsafe abbrev ReplaceM := StateM (PtrMap Expr Expr)

@[inline]
unsafe def cache (key : Expr) (exclusive : Bool)  (result : Expr) : ReplaceM Expr := do
  unless exclusive do
    modify (·.insert key result)
  pure result

@[specialize]
unsafe def replaceUnsafeM (f? : Expr → Option Expr) (e : Expr) : ReplaceM Expr := do
  let rec @[specialize] visit (e : Expr) := do
    -- TODO: We need better control over RC operations to ensure
    -- the following (unsafe) optimization is correctly applied.
    let excl := isExclusiveUnsafe e
    unless excl do
      if let some result := (← get).find? e then
        return result
    match f? e with
      | some eNew => cache e excl eNew
      | none      => match e with
        | .forallE _ d b _   => cache e excl <| e.updateForallE! (← visit d) (← visit b)
        | .lam _ d b _       => cache e excl <| e.updateLambdaE! (← visit d) (← visit b)
        | .mdata _ b         => cache e excl <| e.updateMData! (← visit b)
        | .letE _ t v b _    => cache e excl <| e.updateLet! (← visit t) (← visit v) (← visit b)
        | .app f a           => cache e excl <| e.updateApp! (← visit f) (← visit a)
        | .proj _ _ b        => cache e excl <| e.updateProj! (← visit b)
        | e                  => return e
  visit e

@[inline]
unsafe def replaceUnsafe (f? : Expr → Option Expr) (e : Expr) : Expr :=
  (replaceUnsafeM f? e).run' mkPtrMap

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
