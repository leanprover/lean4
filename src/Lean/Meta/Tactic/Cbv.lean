/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public import Lean.Meta.Tactic.Cbv.Main
public import Lean.Meta.Tactic.Cbv.Util

public section

namespace Lean

builtin_initialize registerTraceClass `Meta.Tactic.cbv
builtin_initialize registerTraceClass `Debug.Meta.Tactic.cbv

end Lean
