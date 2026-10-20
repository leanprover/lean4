/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/
module

prelude
public import Init.Dynamic
public import Lean.Environment
public import Lean.Data.OpenDecl
public import Lean.Data.Options

public section

namespace Lean.Doc

/--
The docstring that a deferred check was recorded in. Identifies the docstring without a source
position, so that editing unrelated text doesn't change the public information of the module.
-/
inductive DeferredCheckSite where
  /-- The check was deferred in docstring of a declaration. -/
  | decl (name : Name)
  /-- The check was deferred from the `n`th module docstring of the module (0-indexed). -/
  | moduleDoc (n : Nat)
deriving Inhabited, Repr, BEq

/--
A recording of the fact that some kind of check could not be carried out when a docstring was
elaborated, due to some missing information that is expected to be available in the future. This is
used for forward references.

The type of the value in `check` selects the handler that carries out the check.

Source positions are not stored because they would shift with edits. Because deferred checks are
part of the public information of a module, this would lead to needless rebuilds. The docstring is
identified by `site`, the reference within it by `index`, and `sourceString` (the reference's source
text) gives readable error messages even without an accurate location.
-/
structure DeferredCheck where
  /-- The docstring or moduledoc in which the reference appears. -/
  site : DeferredCheckSite
  /-- The index of this reference into the deferred checks of its docstring, in source order. -/
  index : Nat
  /-- The reference's source text, to quote in error messages. -/
  sourceString : String
  /-- Modules that should be imported for the check to be meaningful (the reference's `scope`). -/
  imports : Array Name
  /-- The current namespace at the reference site. -/
  currNamespace : Name
  /-- The open declarations in scope at the reference site. -/
  openDecls : List OpenDecl
  /-- The options in effect at the reference site. -/
  options : Options
  /--
  The check-specific data. The name of the type in the `Dynamic` determines which checks are to be
  performed.
   -/
  check : Dynamic

/--
A collection of deferred docstring checks.

While docstrings are part of the server olean for a module, deferred checks are part of the public
information so they can be found by the linter.
-/
builtin_initialize deferredCheckExt :
    PersistentEnvExtension DeferredCheck DeferredCheck (Array DeferredCheck) ←
  registerPersistentEnvExtension {
    mkInitial := pure #[]
    addImportedFn := fun _ => pure #[]
    addEntryFn := Array.push
    exportEntriesFn := id
    asyncMode := .sync
  }

end Lean.Doc
