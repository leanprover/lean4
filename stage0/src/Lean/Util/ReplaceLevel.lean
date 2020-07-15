/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Expr

namespace Lean
namespace Level

partial def replace (f? : Level → Option Level) : Level → Level
| u =>
  match f? u with
  | some v => v
  | none   => match u with
    | max v₁ v₂  _ => mkLevelMax (replace v₁) (replace v₂)
    | imax v₁ v₂ _ => mkLevelIMax (replace v₁) (replace v₂)
    | succ v _     => mkLevelSucc (replace v)
    | _            => u

end Level

namespace Expr

namespace ReplaceLevelImpl

abbrev cacheSize : USize := 8192

structure State :=
(keys    : Array Expr) -- Remark: our "unsafe" implementation relies on the fact that `()` is not a valid Expr
(results : Array Expr)

abbrev ReplaceM := StateM State

@[inline] unsafe def cache (i : USize) (key : Expr) (result : Expr) : ReplaceM Expr := do
modify $ fun s => { keys := s.keys.uset i key lcProof, results := s.results.uset i result lcProof };
pure result

@[specialize] unsafe def replaceUnsafeM (f? : Level → Option Level) (size : USize) : Expr → ReplaceM Expr
| e => do
  c ← get;
  let h := ptrAddrUnsafe e;
  let i := h % size;
  if ptrAddrUnsafe (c.keys.uget i lcProof) == h then
    pure $ c.results.uget i lcProof
  else match e with
      | Expr.forallE _ d b _   => do d ← replaceUnsafeM d; b ← replaceUnsafeM b; cache i e $ e.updateForallE! d b
      | Expr.lam _ d b _       => do d ← replaceUnsafeM d; b ← replaceUnsafeM b; cache i e $ e.updateLambdaE! d b
      | Expr.mdata _ b _       => do b ← replaceUnsafeM b; cache i e $ e.updateMData! b
      | Expr.letE _ t v b _    => do t ← replaceUnsafeM t; v ← replaceUnsafeM v; b ← replaceUnsafeM b; cache i e $ e.updateLet! t v b
      | Expr.app f a _         => do f ← replaceUnsafeM f; a ← replaceUnsafeM a; cache i e $ e.updateApp! f a
      | Expr.proj _ _ b _      => do b ← replaceUnsafeM b; cache i e $ e.updateProj! b
      | Expr.sort u _          => cache i e $ e.updateSort! (u.replace f?)
      | Expr.const n us _      => cache i e $ e.updateConst! (us.map (Level.replace f?))
      | Expr.localE _ _ _ _    => unreachable!
      | e                      => pure e

unsafe def initCache : State :=
{ keys    := mkArray cacheSize.toNat (cast lcProof ()), -- `()` is not a valid `Expr`
  results := mkArray cacheSize.toNat (arbitrary _) }

@[inline] unsafe def replaceUnsafe (f? : Level → Option Level) (e : Expr) : Expr :=
(replaceUnsafeM f? cacheSize e).run' initCache

end ReplaceLevelImpl

@[implementedBy ReplaceLevelImpl.replaceUnsafe]
partial def replaceLevel (f? : Level → Option Level) : Expr → Expr
| e@(Expr.forallE _ d b _)   => let d := replaceLevel d; let b := replaceLevel b; e.updateForallE! d b
| e@(Expr.lam _ d b _)       => let d := replaceLevel d; let b := replaceLevel b; e.updateLambdaE! d b
| e@(Expr.mdata _ b _)       => let b := replaceLevel b; e.updateMData! b
| e@(Expr.letE _ t v b _)    => let t := replaceLevel t; let v := replaceLevel v; let b := replaceLevel b; e.updateLet! t v b
| e@(Expr.app f a _)         => let f := replaceLevel f; let a := replaceLevel a; e.updateApp! f a
| e@(Expr.proj _ _ b _)      => let b := replaceLevel b; e.updateProj! b
| e@(Expr.sort u _)          => e.updateSort! (u.replace f?)
| e@(Expr.const n us _)      => e.updateConst! (us.map (Level.replace f?))
| e                          => e

end Expr
end Lean
