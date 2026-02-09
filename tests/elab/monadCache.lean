import Lean

open Lean

partial def mkTower : Nat → Expr
| 0   => mkConst `a
| n+1 => mkApp2 (mkConst `f) (mkTower n) (mkTower n)

partial def depth : Expr → MonadCacheT Expr Nat CoreM Nat
| e =>
  checkCache e fun _ =>
    match e with
    | Expr.const c [] => pure 1
    | Expr.app f a    => do pure $ Nat.max (← depth f) (← depth a) + 1
    | _               => pure 0

#eval (depth (mkTower 100)).run

partial def visit : Expr → MonadCacheT Expr Expr CoreM Expr
| e =>
  checkCache e fun _ =>
    match e with
    | Expr.const `a [] => pure $ mkConst `b
    | Expr.app f a     => e.updateApp! <$> visit f <*> visit a
    | _                => pure e

#eval (visit (mkTower 4)).run

def tst : CoreM Nat := do
let e ← (visit (mkTower 100)).run; (depth e).run

#eval tst

partial def visitNoCache : Expr → CoreM Expr
| e =>
  match e with
  | Expr.const `a [] => pure $ mkConst `b
  | Expr.app f a     => e.updateApp! <$> visitNoCache f <*> visitNoCache a
  | _                => pure e

-- The following is super slow
-- #eval do e ← visitNoCache (mkTower 30); (depth e).run

def displayConsts (e : Expr) : CoreM Unit :=
e.forEach fun e => match e with
  | Expr.const c _ => do IO.println c
  | _ => pure ()

def tst2 : CoreM Unit := do
let e ← (visit (mkTower 100)).run; displayConsts e

#eval tst2
