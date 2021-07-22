/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.Command
import Lean.Meta.Injective

namespace Lean.Elab.Command

@[builtinCommandElab genInjectiveTheorems] def elabGenInjectiveTheorems : CommandElab := fun stx => do
  let declName ← resolveGlobalConstNoOverload stx[1]
  liftTermElabM none do
    Meta.mkInjectiveTheorems declName

end Lean.Elab.Command
