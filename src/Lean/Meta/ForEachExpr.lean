/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Expr
import Lean.Util.MonadCache
import Lean.Meta.Basic

namespace Lean.Meta
namespace ForEachExpr

abbrev M := MonadCacheT Expr Unit MetaM

mutual

private partial def visitBinder (fn : Expr → MetaM Bool) : Array Expr → Nat → Expr → M Unit
  | fvars, j, Expr.lam n d b c => do
    let d := d.instantiateRevRange j fvars.size fvars;
    visit fn d;
    withLocalDecl n c.binderInfo d fun x =>
      visitBinder fn (fvars.push x) j b
  | fvars, j, Expr.forallE n d b c => do
    let d := d.instantiateRevRange j fvars.size fvars;
    visit fn d;
    withLocalDecl n c.binderInfo d fun x =>
      visitBinder fn (fvars.push x) j b
  | fvars, j, Expr.letE n t v b _ => do
    let t := t.instantiateRevRange j fvars.size fvars;
    visit fn t;
    let v := v.instantiateRevRange j fvars.size fvars;
    visit fn v;
    withLetDecl n t v fun x =>
      visitBinder fn (fvars.push x) j b
  | fvars, j, e => visit fn $ e.instantiateRevRange j fvars.size fvars

partial def visit (fn : Expr → MetaM Bool) (e : Expr) : M Unit :=
  checkCache e fun _ => do
    if (← liftM (fn e)) then
      match e with
      | Expr.forallE _ _ _ _   => visitBinder fn #[] 0 e
      | Expr.lam _ _ _ _       => visitBinder fn #[] 0 e
      | Expr.letE _ _ _ _ _    => visitBinder fn #[] 0 e
      | Expr.app f a _         => visit fn f; visit fn a
      | Expr.mdata _ b _       => visit fn b
      | Expr.proj _ _ b _      => visit fn b
      | _                      => pure ()

end

end ForEachExpr

/-- Similar to `Expr.forEach'`, but creates free variables whenever going inside of a binder. -/
def forEachExpr' (e : Expr) (f : Expr → MetaM Bool) : MetaM Unit :=
  ForEachExpr.visit f e |>.run

/-- Similar to `Expr.forEach`, but creates free variables whenever going inside of a binder. -/
def forEachExpr (e : Expr) (f : Expr → MetaM Unit) : MetaM Unit :=
  forEachExpr' e fun e => do
    f e
    pure true

end Lean.Meta
