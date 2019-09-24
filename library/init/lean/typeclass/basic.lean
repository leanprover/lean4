/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam, Leonardo de Moura
-/
prelude
import init.lean.environment

namespace Lean
namespace TypeClass

/- Entry point for the `#synth` command used for testing. -/
@[export lean_typeclass_synth_command]
def synth_command (env : Environment) (e : Expr) : ExceptT String Id Expr :=
Except.error "not implemented yet"

end TypeClass
end Lean
