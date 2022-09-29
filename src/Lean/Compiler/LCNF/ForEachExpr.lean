/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Util.ForEachExpr
import Lean.Compiler.LCNF.Basic

namespace Lean.Compiler.LCNF

partial def Code.forEachExpr [STWorld ω m] [MonadLiftT (ST ω) m] [Monad m] (f : Expr → m Unit) (c : Code) (skipTypes := false) : m Unit := do
  visit c |>.run
where
  visit (c : Code) : MonadCacheT Expr Unit m Unit := do
    match c with
    | .let decl k =>
      visitType decl.type
      visitExpr decl.value
      visit k
    | .jp decl k | .fun decl k =>
      visitType decl.type
      decl.params.forM visitParam
      visit decl.value
      visit k
    | .unreach type => visitType type
    | .return .. => return ()
    | .jmp _ args => args.forM visitExpr
    | .cases c => visitType c.resultType; c.alts.forM fun alt => do
      match alt with
      | .default k => visit k
      | .alt _ ps k => ps.forM visitParam; visit k

  visitParam (p : Param) : MonadCacheT Expr Unit m Unit :=
    visitType p.type

  visitExpr (e : Expr) : MonadCacheT Expr Unit m Unit :=
    ForEachExpr.visit (fun e => f e *> return true)  e

  visitType (e : Expr) : MonadCacheT Expr Unit m Unit :=
    unless skipTypes do
      visitExpr e

def Decl.forEachExpr [STWorld ω m] [MonadLiftT (ST ω) m] [Monad m] (f : Expr → m Unit) (decl : Decl) (skipTypes := false) : m Unit := do
  visit |>.run
where
  visit : MonadCacheT Expr Unit m Unit := do
    Code.forEachExpr.visitType f decl.type (skipTypes := skipTypes)
    decl.params.forM (Code.forEachExpr.visitParam f (skipTypes := skipTypes))
    Code.forEachExpr.visit f decl.value (skipTypes := skipTypes)

end Lean.Compiler.LCNF