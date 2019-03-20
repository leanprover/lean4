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
def mkLcProof (pred : Expr) := Expr.app (Expr.const `lcProof []) pred

end Compiler
end Lean
