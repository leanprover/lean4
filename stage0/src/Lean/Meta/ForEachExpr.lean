/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Expr
import Lean.Util.MonadCache
import Lean.Meta.Basic

namespace Lean
namespace Meta
namespace ForEachExpr
abbrev M := MonadCacheT Expr Unit MetaM

@[specialize] private partial def visitBinder (visit : Expr → M Unit) : Array Expr → Nat → Expr → M Unit
| fvars, j, Expr.lam n d b c => do
  let d := d.instantiateRevRange j fvars.size fvars;
  visit d;
  withLocalDecl n c.binderInfo d fun x =>
    visitBinder (fvars.push x) j b
| fvars, j, Expr.forallE n d b c => do
  let d := d.instantiateRevRange j fvars.size fvars;
  visit d;
  withLocalDecl n c.binderInfo d fun x =>
    visitBinder (fvars.push x) j b
| fvars, j, Expr.letE n t v b _ => do
  let t := t.instantiateRevRange j fvars.size fvars;
  visit t;
  let v := v.instantiateRevRange j fvars.size fvars;
  visit v;
  withLetDecl n t v fun x =>
    visitBinder (fvars.push x) j b
| fvars, j, e => visit $ e.instantiateRevRange j fvars.size fvars

partial def visit (f : Expr → MetaM Bool) : Expr → M Unit
| e => checkCache e fun e =>
  condM (not <$> liftM (f e)) (pure ()) do
    match e with
    | Expr.forallE _ _ _ _   => visitBinder visit #[] 0 e
    | Expr.lam _ _ _ _       => visitBinder visit #[] 0 e
    | Expr.letE _ _ _ _ _    => visitBinder visit #[] 0 e
    | Expr.app f a _         => do visit f; visit a
    | Expr.mdata _ b _       => visit b
    | Expr.proj _ _ b _      => visit b
    | _                      => pure ()
end ForEachExpr

def forEachExprImp' (e : Expr) (f : Expr → MetaM Bool) : MetaM Unit :=
(ForEachExpr.visit f e).run

/-- Similar to `Expr.forEach'`, but creates free variables whenever going inside of a binder. -/
def forEachExpr' {m} [MonadLiftT MetaM m] (e : Expr) (f : Expr → MetaM Bool) : m Unit :=
liftM $ forEachExprImp' e f

/-- Similar to `Expr.forEach`, but creates free variables whenever going inside of a binder. -/
def forEachExpr {m} [MonadLiftT MetaM m] (e : Expr) (f : Expr → MetaM Unit) : m Unit :=
forEachExpr' e (fun e => do f e; pure true)

end Meta
end Lean
