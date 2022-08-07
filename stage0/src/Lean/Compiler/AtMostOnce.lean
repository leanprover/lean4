/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Environment

namespace Lean.Compiler

namespace atMostOnce

structure AtMostOnceData where
  found : Bool
  result : Bool

def Visitor := AtMostOnceData → AtMostOnceData

@[inline] def seq (f g : Visitor) : Visitor := fun d =>
  match f d with
  | ⟨found, false⟩ => ⟨found, false⟩
  | other          => g other

instance : AndThen Visitor where
  andThen a b := seq a (b ())

@[inline] def skip : Visitor := id

@[inline] def visitFVar (x y : FVarId) : Visitor
  | d@{result := false, ..} => d
  | {found := false, result := true} => {found := x == y, result := true}
  | {found := true,  result := true} => {found := true, result := x != y}

def visit (x : FVarId) : Expr → Visitor
  | Expr.fvar y          => visitFVar y x
  | Expr.app f a         => visit x a >> visit x f
  | Expr.lam _ d b _     => visit x d >> visit x b
  | Expr.forallE _ d b _ => visit x d >> visit x b
  | Expr.letE _ t v b _  => visit x t >> visit x v >> visit x b
  | Expr.mdata _ e       => visit x e
  | Expr.proj _ _ e      => visit x e
  | _                    => skip

end atMostOnce

open atMostOnce (visit) in
/-- Return true iff the free variable with id `x` occurs at most once in `e` -/
@[export lean_at_most_once]
def atMostOnce (e : Expr) (x : FVarId) : Bool :=
  let {result := result, ..} := visit x e {found := false, result := true}
  result

end Lean.Compiler
