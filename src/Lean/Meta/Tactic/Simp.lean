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

namespace Lean

builtin_initialize registerTacticTraceClass `simp
builtin_initialize registerTraceClass `simp.congr (inherited := true) (descr := "the `simp` tactic congruence rules")
builtin_initialize registerTraceClass `simp.discharge (inherited := true) (descr := "the `simp` tactic discharger")
builtin_initialize registerTraceClass `simp.rewrite (inherited := true) (descr := "the `simp` tactic rewrite step")
builtin_initialize registerTraceClass `simp.unify (inherited := true) (descr := "the `simp` tactic unifier")
builtin_initialize registerTraceClass `simp.ground (inherited := true) (descr := "the `simp` tactic ground evaluator")
builtin_initialize registerTraceClass `simp.numSteps (descr := "the `simp` tactic number of steps")
builtin_initialize registerTraceClass `simp.heads (descr := "the `simp` tactic head symbols")
builtin_initialize registerTraceClass `simp.debug (descr := "the `simp` tactic debugger")
builtin_initialize registerTraceClass `simp.debug.congr (inherited := true) (descr := "the `simp` tactic congruence rule debugger")

end Lean
