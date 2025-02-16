/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Simp.SimpTheorems
import Lean.Meta.Tactic.Simp.SimpCongrTheorems
import Lean.Meta.Tactic.Simp.Types
import Lean.Meta.Tactic.Simp.Main
import Lean.Meta.Tactic.Simp.Rewrite
import Lean.Meta.Tactic.Simp.SimpAll
import Lean.Meta.Tactic.Simp.Simproc
import Lean.Meta.Tactic.Simp.BuiltinSimprocs
import Lean.Meta.Tactic.Simp.RegisterCommand
import Lean.Meta.Tactic.Simp.Attr
import Lean.Meta.Tactic.Simp.Diagnostics
import Lean.Meta.Tactic.Simp.Arith

namespace Lean

builtin_initialize registerTraceClass `Meta.Tactic.simp
builtin_initialize registerTraceClass `Meta.Tactic.simp.congr (inherited := true)
builtin_initialize registerTraceClass `Meta.Tactic.simp.discharge (inherited := true)
builtin_initialize registerTraceClass `Meta.Tactic.simp.rewrite (inherited := true)
builtin_initialize registerTraceClass `Meta.Tactic.simp.unify (inherited := true)
builtin_initialize registerTraceClass `Meta.Tactic.simp.ground (inherited := true)
builtin_initialize registerTraceClass `Meta.Tactic.simp.numSteps
builtin_initialize registerTraceClass `Meta.Tactic.simp.heads
builtin_initialize registerTraceClass `Debug.Meta.Tactic.simp
builtin_initialize registerTraceClass `Debug.Meta.Tactic.simp.congr (inherited := true)

end Lean
