/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julia M. Himmel
-/
module

prelude
public import Lean.Linter.InternalModule

namespace Lean.Linter

/-- Record the linters that are enabled when building Lean itself as members of the
`linter.coreInternal` set, so that they pick up the set-membership fallback in `getLinterValue`.
The `linter.coreInternal` option itself is registered as a builtin option in `Lean.Linter.Init`. -/
builtin_initialize
  addBuiltinLinterSet `linter.coreInternal <|
    NameSet.empty
      |>.insert `linter.coreInternal.internalModule
      |>.insert `linter.csimpNoncomputable
      |>.insert `linter.redundantVisibility

end Lean.Linter
