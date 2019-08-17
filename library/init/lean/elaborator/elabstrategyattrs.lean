/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.attributes

namespace Lean
/-
Elaborator strategies available in the Lean3 elaborator.
We want to support a more general approach, but we need to provide
the strategy selection attributes while we rely on the Lean3 elaborator.
-/
inductive ElaboratorStrategy
| simple | withExpectedType | asEliminator

instance ElaboratorStrategy.inhabited : Inhabited ElaboratorStrategy :=
⟨ElaboratorStrategy.withExpectedType⟩

def mkElaboratorStrategyAttrs : IO (EnumAttributes ElaboratorStrategy) :=
registerEnumAttributes `elaboratorStrategy
  [(`elabWithExpectedType, "instructs elaborator that the arguments of the function application (f ...) should be elaborated using information about the expected type", ElaboratorStrategy.withExpectedType),
   (`elabSimple, "instructs elaborator that the arguments of the function application (f ...) should be elaborated from left to right, and without propagating information from the expected type to its arguments", ElaboratorStrategy.simple),
   (`elabAsEliminator, "instructs elaborator that the arguments of the function application (f ...) should be elaborated as f were an eliminator", ElaboratorStrategy.asEliminator)]

@[init mkElaboratorStrategyAttrs]
constant elaboratorStrategyAttrs : EnumAttributes ElaboratorStrategy := default _

@[export lean_get_elaborator_strategy]
def getElaboratorStrategy (env : Environment) (n : Name) : Option ElaboratorStrategy :=
elaboratorStrategyAttrs.getValue env n

end Lean
