/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Expr
import Lean.Util.MonadCache

namespace Lean
/-!
Remark: we cannot use the caching trick used at `FindExpr` and `ReplaceExpr` because they
may visit the same expression multiple times if they are stored in different memory
addresses. Note that the following code is parametric in a monad `m`.
-/

variable {ω : Type} {m : Type → Type} [STWorld ω m] [MonadLiftT (ST ω) m] [Monad m]
namespace ForEachExpr
def visit (g : Expr → m Bool) (e : Expr) : MonadCacheT Expr Unit m Unit :=
  checkCache e fun _ => do
    if (← g e) then
      match e with
      | Expr.forallE _ d b _   => do visit g d; visit g b
      | Expr.lam _ d b _       => do visit g d; visit g b
      | Expr.letE _ t v b _    => do visit g t; visit g v; visit g b
      | Expr.app f a           => do visit g f; visit g a
      | Expr.mdata _ b         => visit g b
      | Expr.proj _ _ b        => visit g b
      | _                      => pure ()

end ForEachExpr

/-- Apply `f` to each sub-expression of `e`. If `f t` returns false, then t's children are not visited. -/
@[inline] def Expr.forEach' (e : Expr) (f : Expr → m Bool) : m Unit :=
  (ForEachExpr.visit f e).run

@[inline] def Expr.forEach (e : Expr) (f : Expr → m Unit) : m Unit :=
  e.forEach' fun e => do f e; pure true

end Lean
