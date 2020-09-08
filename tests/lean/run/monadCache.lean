import Lean
open Lean

def mkTower : Nat → Expr
| 0   => mkConst `a
| n+1 => mkApp2 (mkConst `f) (mkTower n) (mkTower n)

partial def depth : Expr → MonadCacheT Expr Nat CoreM Nat
| e =>
  checkCache e fun e =>
    match e with
    | Expr.const c [] _ => pure 1
    | Expr.app f a _    => do d₁ ← depth f; d₂ ← depth a; pure $ Nat.max d₁ d₂ + 1
    | _                 => pure 0

#eval (depth (mkTower 100)).run

partial def visit : Expr → MonadCacheT Expr Expr CoreM Expr
| e =>
  checkCache e fun e =>
    match e with
    | Expr.const `a [] _ => pure $ mkConst `b
    | Expr.app f a _     => e.updateApp! <$> visit f <*> visit a
    | _                  => pure e

#eval (visit (mkTower 4)).run

#eval do e ← (visit (mkTower 100)).run; (depth e).run

partial def visitNoCache : Expr → CoreM Expr
| e =>
  match e with
  | Expr.const `a [] _ => pure $ mkConst `b
  | Expr.app f a _     => e.updateApp! <$> visitNoCache f <*> visitNoCache a
  | _                  => pure e

-- The following is super slow
-- #eval do e ← visitNoCache (mkTower 30); (depth e).run
