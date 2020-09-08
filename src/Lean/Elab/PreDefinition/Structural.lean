/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.PreDefinition.Basic

namespace Lean
namespace Elab
open Meta

def structuralRecursion (preDefs : Array PreDefinition) : TermElabM Bool :=
if preDefs.size != 1 then
  pure false
else do
  let preDef := preDefs.get! 0;
  trace `Elab.definition fun _ => preDef.declName ++ ":=\n" ++ preDef.value;
  throwError "WIP"

end Elab
end Lean
