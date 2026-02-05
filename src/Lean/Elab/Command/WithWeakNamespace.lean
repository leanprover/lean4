/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Daniel Selsam, Gabriel Ebner
-/
module

prelude
public import Lean.Elab.Command

namespace Lean.Elab.Command

/-- Adds the name to the namespace, `_root_`-aware.
```
resolveNamespaceRelative `A `B.b == `A.B.b
resolveNamespaceRelative `A `_root_.B.c == `B.c
```
-/
def resolveNamespaceRelative (ns : Name) : Name → Name
  | `_root_ => Name.anonymous
  | Name.str n s .. => Name.mkStr (resolveNamespaceRelative ns n) s
  | Name.num n i .. => Name.mkNum (resolveNamespaceRelative ns n) i
  | Name.anonymous => ns

/-- Changes the current namespace without causing scoped things to go out of scope -/
def withWeakNamespace {α : Type} (ns : Name) (m : CommandElabM α) : CommandElabM α := do
  let old ← getCurrNamespace
  let ns := resolveNamespaceRelative old ns
  modify fun s ↦ { s with env := s.env.registerNamespace ns }
  modifyScope ({ · with currNamespace := ns })
  try m finally modifyScope ({ · with currNamespace := old })

@[builtin_command_elab Parser.Command.withWeakNamespace]
def elabWithWeakNamespace : CommandElab
  | `(Parser.Command.withWeakNamespace| with_weak_namespace $ns:ident $cmd) =>
    withWeakNamespace ns.getId (elabCommand cmd)
  | _ => throwUnsupportedSyntax

end Lean.Elab.Command
