/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Lean.ToExpr
public import Lean.Util.Path
public import Lean.Elab.Term
meta import Lean.Elab.Term

public section

open Lean

/--
Term elaborator that retrieves the current `SearchPath`.

Typical usage is `searchPathRef.set compile_time_search_path%`.

This must not be used in files that are potentially compiled on another machine and then imported.
(That is, if used in an imported file it will embed the search path from whichever machine
compiled the `.olean`.)
-/
@[deprecated "Deprecated without replacement." (since := "2025-02-10")]
elab "compile_time_search_path%" : term => do
  logWarning "`compile_time_search_path%` is deprecated; use `initSearchPath (← findSysroot)` instead."
  return toExpr (← searchPathRef.get)
