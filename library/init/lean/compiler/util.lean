/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.expr

namespace lean
namespace compiler

def neutralExpr : expr       := expr.const `_neutral []
def unreachableExpr : expr   := expr.const `_unreachable []
def objectType : expr        := expr.const `_obj []
def voidType : expr          := expr.const `_void []
def mkLcProof (pred : expr) := expr.app (expr.const `lcProof []) pred

end compiler
end lean
