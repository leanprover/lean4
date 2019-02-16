/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.expr

namespace lean
namespace compiler

def neutral_expr : expr       := expr.const `_neutral []
def unreachable_expr : expr   := expr.const `_unreachable []
def object_type : expr        := expr.const `_obj []
def void_type : expr          := expr.const `_void []
def mk_lc_proof (pred : expr) := expr.app (expr.const `lc_proof []) pred

end compiler
end lean
