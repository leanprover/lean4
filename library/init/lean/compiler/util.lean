/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.expr

namespace Lean
namespace Compiler

def neutralExpr : Expr       := Expr.const `_neutral []
def unreachableExpr : Expr   := Expr.const `_unreachable []
def objectType : Expr        := Expr.const `_obj []
def voidType : Expr          := Expr.const `_void []
def mkLcProof (pred : Expr)  := Expr.app (Expr.const `lcProof []) pred

namespace atMostOnce

structure AtMostOnceData :=
(found result : Bool)

def Visitor := AtMostOnceData → AtMostOnceData

@[inline] def seq (f g : Visitor) : Visitor :=
λ d, match f d with
| ⟨found, false⟩ := ⟨found, false⟩
| other          := g other

@[inline] def skip : Visitor := id

@[inline] def visitFVar (x y : Name) : Visitor
| d@{result := false, ..}  := d
| {found := false, result := true} := {found := x == y, result := true}
| {found := true,  result := true} := {found := true, result := x != y}

local infix *> := seq

def visit (x : Name) : Expr → Visitor
| (Expr.fvar y)       := visitFVar y x
| (Expr.app f a)      := visit a *> visit f
| (Expr.lam _ _ d b)  := visit d *> visit b
| (Expr.pi _ _ d b)   := visit d *> visit b
| (Expr.elet _ t v b) := visit t *> visit v *> visit b
| (Expr.mdata _ e)    := visit e
| (Expr.proj _ _ e)   := visit e
| _                   := skip

end atMostOnce

/-- Return true iff the free variable with id `x` occurs at most once in `e` -/
@[export lean.at_most_once_core]
def atMostOnce (e : Expr) (x : Name) : Bool :=
let {result := result, ..} := atMostOnce.visit x e {found := false, result := true} in
result

end Compiler
end Lean
