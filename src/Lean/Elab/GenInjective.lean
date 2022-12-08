/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.Command
import Lean.Meta.Injective

namespace Lean.Elab.Command

@[builtin_command_elab genInjectiveTheorems] def elabGenInjectiveTheorems : CommandElab := fun stx => do
  let declName ← resolveGlobalConstNoOverloadWithInfo stx[1]
  liftTermElabM do
    Meta.mkInjectiveTheorems declName

end Lean.Elab.Command
