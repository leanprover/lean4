/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public import Lean.Linter.Extra.DupNamespace
public import Lean.Linter.Extra.UnnecessarySeqFocus
public import Lean.Linter.Extra.UnreachableTactic
public import Lean.Linter.Extra.UnusedDecidableInType

namespace Lean.Linter

/-- Record the four extra linters as members of the `linter.extra` set, so that they pick up the
set-membership fallback in `getLinterValue`. The `linter.extra` option itself is registered as a
builtin option in `Lean.Linter.Init`. -/
builtin_initialize
  addBuiltinLinterSet `linter.extra <|
    NameSet.empty
      |>.insert `linter.extra.dupNamespace
      |>.insert `linter.extra.unnecessarySeqFocus
      |>.insert `linter.extra.unreachableTactic
      |>.insert `linter.extra.unusedDecidableInType

end Lean.Linter
