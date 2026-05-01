/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public import Init.Notation

public section

/-- `@[builtin_nolint linterName*]` omits the tagged declaration from being checked by
the named builtin linters in `lake builtin-lint`. -/
syntax (name := builtin_nolint) "builtin_nolint" (ppSpace ident)+ : attr
