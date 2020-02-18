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
(keys : Array Expr)

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

def initCache : State :=
{ keys    := mkArray cacheSize.toNat (arbitrary _) }

@[inline] unsafe def findExprUnsafe? (p : Expr → Bool) (e : Expr) : Option Expr :=
(findM? p cacheSize e).run' initCache

end FindImpl

@[implementedBy FindImpl.findExprUnsafe?]
partial def findExpr? (p : Expr → Bool) : Expr → Option Expr
| e =>
  /- This is a reference implementation for the unsafe one above -/
  if p e then some e
  else match e with
    | Expr.forallE _ d b _   => findExpr? d <|> findExpr? b
    | Expr.lam _ d b _       => findExpr? d <|> findExpr? b
    | Expr.mdata _ b _       => findExpr? b
    | Expr.letE _ t v b _    => findExpr? t <|> findExpr? v <|> findExpr? b
    | Expr.app f a _         => findExpr? f <|> findExpr? a
    | Expr.proj _ _ b _      => findExpr? b
    | e                      => none

end Expr
end Lean
