/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.PreDefinition.Basic
import Lean.Elab.PreDefinition.Structural.Basic

namespace Lean.Elab.Structural

def mkEqns (preDef : PreDefinition) : TermElabM Unit := do
  trace[Elab.definition.structural.eqns] "mkEqns:\n{preDef.value}"
  return ()

builtin_initialize
  registerTraceClass `Elab.definition.structural.eqns

end Lean.Elab.Structural
