/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.Lean.Data.Occurrences
import Init.Lean.HeadIndex
import Init.Lean.Meta.ExprDefEq

namespace Lean
namespace Meta

private partial def kabstractAux (occs : Occurrences) (p : Expr) (pHeadIdx : HeadIndex) (pNumArgs : Nat) : Expr → Nat → StateT Nat MetaM Expr
| e, offset =>
  let visitChildren : Unit → StateT Nat MetaM Expr := fun _ =>
    match e with
    | Expr.app f a _       => do f ← kabstractAux f offset; a ← kabstractAux a offset; pure $ e.updateApp! f a
    | Expr.mdata _ b _     => do b ← kabstractAux b offset; pure $ e.updateMData! b
    | Expr.proj _ _ b _    => do b ← kabstractAux b offset; pure $ e.updateProj! b
    | Expr.letE _ t v b _  => do t ← kabstractAux t offset; v ← kabstractAux v offset; b ← kabstractAux b (offset+1); pure $ e.updateLet! t v b
    | Expr.lam _ d b _     => do d ← kabstractAux d offset; b ← kabstractAux b (offset+1); pure $ e.updateLambdaE! d b
    | Expr.forallE _ d b _ => do d ← kabstractAux d offset; b ← kabstractAux b (offset+1); pure $ e.updateForallE! d b
    | e                    => pure e;
  if e.hasLooseBVars then visitChildren ()
  else if e.toHeadIndex == pHeadIdx && e.headNumArgs == pNumArgs then
    condM (liftM $ isDefEq e p)
      (do i ← get;
          set (i+1);
          if occs.contains i then
            pure (mkBVar offset)
          else
            visitChildren ())
      (visitChildren ())
  else
    visitChildren ()

def kabstract (e : Expr) (p : Expr) (occs : Occurrences := Occurrences.all) : MetaM Expr :=
(kabstractAux occs p p.toHeadIndex p.headNumArgs e 0).run' 1

end Meta
end Lean
