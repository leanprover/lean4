/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Control.Option
import Init.Lean.Expr

namespace Lean
namespace Expr

namespace FindImpl

abbrev cacheSize : USize := 8192

structure State :=
(keys : Array Expr) -- Remark: our "unsafe" implementation relies on the fact that `()` is not a valid Expr

abbrev FindM := StateM State

@[inline] unsafe def visited (e : Expr) (size : USize) : FindM Bool := do
s ← get;
let h := ptrAddrUnsafe e;
let i := h % size;
let k := s.keys.uget i lcProof;
if ptrAddrUnsafe k == h then pure true
else do
  modify $ fun s => { keys := s.keys.uset i e lcProof };
  pure false

@[specialize] unsafe partial def findM? (p : Expr → Bool) (size : USize) : Expr → OptionT FindM Expr
| e => condM (liftM $ visited e size) failure $
  if p e then pure e
  else match e with
    | Expr.forallE _ d b _   => findM? d <|> findM? b
    | Expr.lam _ d b _       => findM? d <|> findM? b
    | Expr.mdata _ b _       => findM? b
    | Expr.letE _ t v b _    => findM? t <|> findM? v <|> findM? b
    | Expr.app f a _         => findM? f <|> findM? a
    | Expr.proj _ _ b _      => findM? b
    | e                      => failure

unsafe def initCache : State :=
{ keys    := mkArray cacheSize.toNat (cast lcProof ()) }

@[inline] unsafe def findUnsafe? (p : Expr → Bool) (e : Expr) : Option Expr :=
(findM? p cacheSize e).run' initCache

end FindImpl

@[implementedBy FindImpl.findUnsafe?]
partial def find? (p : Expr → Bool) : Expr → Option Expr
| e =>
  /- This is a reference implementation for the unsafe one above -/
  if p e then some e
  else match e with
    | Expr.forallE _ d b _   => find? d <|> find? b
    | Expr.lam _ d b _       => find? d <|> find? b
    | Expr.mdata _ b _       => find? b
    | Expr.letE _ t v b _    => find? t <|> find? v <|> find? b
    | Expr.app f a _         => find? f <|> find? a
    | Expr.proj _ _ b _      => find? b
    | e                      => none

end Expr
end Lean
