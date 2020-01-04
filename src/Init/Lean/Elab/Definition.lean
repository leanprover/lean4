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

structure DefViewCore :=
(kind          : DefKind)
(ref           : Syntax)
(modifiers     : Modifiers)
(declId        : Syntax)
(binders       : Syntax)
(type          : Option Syntax := none)
(val           : Option Syntax := none)

structure DefView extends DefViewCore :=
(currNamespace : Name)
(name          : Name)
(univNames     : List Name)
(vars          : Array Expr)

end Command

namespace Term

def elabDefTypeVal (view : Command.DefView) : TermElabM (Expr × Option Expr) := do
dbgTrace (toString view.currNamespace ++ " " ++ toString view.name ++ " " ++ toString view.univNames);
pure (arbitrary _, none)

end Term

namespace Command

def elabDefCore (view : DefViewCore) : CommandElabM Unit :=
withDeclId view.declId $ fun name univNames => do
  currNamespace ← getCurrNamespace;
  runTermElabM $ fun vars => do
    (type, val?) ← Term.elabDefTypeVal {
      currNamespace := currNamespace,
      name          := name,
      univNames     := univNames,
      vars          := vars,
      .. view };
    pure ()

end Command
end Elab
end Lean
