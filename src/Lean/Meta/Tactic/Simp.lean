/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.Tactic.Simp.SimpTheorems
public import Lean.Meta.Tactic.Simp.SimpCongrTheorems
public import Lean.Meta.Tactic.Simp.Types
public import Lean.Meta.Tactic.Simp.Main
public import Lean.Meta.Tactic.Simp.Rewrite
public import Lean.Meta.Tactic.Simp.SimpAll
public import Lean.Meta.Tactic.Simp.Simproc
public import Lean.Meta.Tactic.Simp.BuiltinSimprocs
public import Lean.Meta.Tactic.Simp.RegisterCommand
public import Lean.Meta.Tactic.Simp.Attr
public import Lean.Meta.Tactic.Simp.Diagnostics
public import Lean.Meta.Tactic.Simp.Arith

public section

namespace Lean

builtin_initialize registerTraceClass `Meta.Tactic.simp
builtin_initialize registerTraceClass `Meta.Tactic.simp.congr (inherited := true)
builtin_initialize registerTraceClass `Meta.Tactic.simp.discharge (inherited := true)
builtin_initialize registerTraceClass `Meta.Tactic.simp.rewrite (inherited := true)
builtin_initialize registerTraceClass `Meta.Tactic.simp.unify (inherited := true)
builtin_initialize registerTraceClass `Meta.Tactic.simp.ground (inherited := true)
builtin_initialize registerTraceClass `Meta.Tactic.simp.loopProtection (inherited := true)
builtin_initialize registerTraceClass `Meta.Tactic.simp.numSteps
builtin_initialize registerTraceClass `Meta.Tactic.simp.heads
builtin_initialize registerTraceClass `Debug.Meta.Tactic.simp
builtin_initialize registerTraceClass `Debug.Meta.Tactic.simp.congr (inherited := true)

end Lean
