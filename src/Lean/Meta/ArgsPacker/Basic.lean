/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

prelude
import Init.Data.Array.Basic

/-!
The basic data type and namespace for the `Lean.Meta.ArgsPacker` modules.

This is separated so that `Lean.Elab.PreDefinition.WF.Eqns` can include the
type in `EqnInfos` without depending on full module with operations.
-/

namespace Lean.Meta

/--
The metadata required for the operation in the `Lean.Meta.ArgsPacker` module; see
the module docs there for an overview.
-/
structure ArgsPacker where
  /--
  Variable names to use when unpacking a packed argument.

  Crucially, the size of this array also indicates the number of functions to pack, and
  the length of each array the arity.
  -/
  varNamess : Array (Array Name)
  deriving Inhabited

end Lean.Meta
