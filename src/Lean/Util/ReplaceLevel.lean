/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Expr

namespace Lean
namespace Level

partial def replace (f? : Level → Option Level) (u : Level) : Level :=
  match f? u with
  | some v => v
  | none   => match u with
    | max v₁ v₂  => mkLevelMax' (replace f? v₁) (replace f? v₂)
    | imax v₁ v₂ => mkLevelIMax' (replace f? v₁) (replace f? v₂)
    | succ v     => mkLevelSucc (replace f? v)
    | _          => u

end Level

namespace Expr

namespace ReplaceLevelImpl

abbrev cacheSize : USize := 8192 - 1

structure State where
  keys    : Array Expr -- Remark: our "unsafe" implementation relies on the fact that `()` is not a valid Expr
  results : Array Expr

abbrev ReplaceM := StateM State

unsafe def cache (i : USize) (key : Expr) (result : Expr) : ReplaceM Expr := do
  modify fun s => { keys := s.keys.uset i key lcProof, results := s.results.uset i result lcProof };
  pure result

unsafe def replaceUnsafeM (f? : Level → Option Level) (size : USize) (e : Expr) : ReplaceM Expr := do
  let rec visit (e : Expr) := do
    let c ← get
    let h := ptrAddrUnsafe e
    let i := h % size
    if ptrAddrUnsafe (c.keys.uget i lcProof) == h then
      pure <| c.results.uget i lcProof
    else match e with
        | Expr.forallE _ d b _   => cache i e <| e.updateForallE! (← visit d) (← visit b)
        | Expr.lam _ d b _       => cache i e <| e.updateLambdaE! (← visit d) (← visit b)
        | Expr.mdata _ b         => cache i e <| e.updateMData! (← visit b)
        | Expr.letE _ t v b _    => cache i e <| e.updateLet! (← visit t) (← visit v) (← visit b)
        | Expr.app f a           => cache i e <| e.updateApp! (← visit f) (← visit a)
        | Expr.proj _ _ b        => cache i e <| e.updateProj! (← visit b)
        | Expr.sort u            => cache i e <| e.updateSort! (u.replace f?)
        | Expr.const _ us        => cache i e <| e.updateConst! (us.map (Level.replace f?))
        | e                      => pure e
  visit e

unsafe def initCache : State :=
  { keys    := .replicate cacheSize.toNat (cast lcProof ()), -- `()` is not a valid `Expr`
    results := .replicate cacheSize.toNat default }

unsafe def replaceUnsafe (f? : Level → Option Level) (e : Expr) : Expr :=
  (replaceUnsafeM f? cacheSize e).run' initCache

end ReplaceLevelImpl

@[implemented_by ReplaceLevelImpl.replaceUnsafe]
partial def replaceLevel (f? : Level → Option Level) : Expr → Expr
  | e@(Expr.forallE _ d b _)   => let d := replaceLevel f? d; let b := replaceLevel f? b; e.updateForallE! d b
  | e@(Expr.lam _ d b _)       => let d := replaceLevel f? d; let b := replaceLevel f? b; e.updateLambdaE! d b
  | e@(Expr.mdata _ b)         => let b := replaceLevel f? b; e.updateMData! b
  | e@(Expr.letE _ t v b _)    => let t := replaceLevel f? t; let v := replaceLevel f? v; let b := replaceLevel f? b; e.updateLet! t v b
  | e@(Expr.app f a)           => let f := replaceLevel f? f; let a := replaceLevel f? a; e.updateApp! f a
  | e@(Expr.proj _ _ b)        => let b := replaceLevel f? b; e.updateProj! b
  | e@(Expr.sort u)            => e.updateSort! (u.replace f?)
  | e@(Expr.const _ us)        => e.updateConst! (us.map (Level.replace f?))
  | e                          => e

end Expr
end Lean
