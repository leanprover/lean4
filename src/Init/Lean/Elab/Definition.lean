/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Init.Lean.Elab.DeclModifiers

namespace Lean
namespace Elab

namespace Command

inductive DefKind
| «def» | «theorem» | «example» | «opaque» | «axiom»

structure DefView :=
(kind          : DefKind)
(ref           : Syntax)
(modifiers     : Modifiers)
(declId        : Syntax)
(binders       : Syntax)
(type?         : Option Syntax := none)
(val?          : Option Syntax := none)

def elabDefLike (view : DefView) : CommandElabM Unit :=
withDeclId view.declId $ fun name => do
  currNamespace ← getCurrNamespace;
  type ← runTermElabM $ fun vars => Term.elabBinders view.binders.getArgs $ fun xs =>
    match view.type? with
    | some typeStx => do
      type ← Term.elabType typeStx;
      Term.synthesizeSyntheticMVars false;
      type ← Term.instantiateMVars typeStx type;
      -- TODO: unassigned universe metavariables to new parameters
      -- TODO: if theorem, filter unused vars
      pure type
    | none => Term.mkFreshTypeMVar view.binders;
  dbgTrace (">>> " ++ toString type);
  pure ()

end Command
end Elab
end Lean
