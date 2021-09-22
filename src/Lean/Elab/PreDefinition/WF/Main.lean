/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.PreDefinition.Basic
import Lean.Elab.PreDefinition.WF.PackDomain

namespace Lean.Elab
open WF
open Meta

def wfRecursion (preDefs : Array PreDefinition) (terminationBy? : Option Syntax) : TermElabM Bool := do
  withoutModifyingEnv do
    for preDef in preDefs do
      addAsAxiom preDef
    let unaryPreDefs ← packDomain preDefs
    for preDef in unaryPreDefs do
      check preDef.value -- TODO: remove
      trace[Elab.definition.wf] "{preDef.declName}, {preDef.levelParams}, {preDef.value}"
  -- TODO
  throwError "well founded recursion has not been implemented yet"

builtin_initialize registerTraceClass `Elab.definition.wf

end Lean.Elab
