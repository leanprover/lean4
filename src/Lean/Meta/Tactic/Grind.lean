/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Attr
import Lean.Meta.Tactic.Grind.RevertAll
import Lean.Meta.Tactic.Grind.Types
import Lean.Meta.Tactic.Grind.Preprocessor
import Lean.Meta.Tactic.Grind.Util
import Lean.Meta.Tactic.Grind.Cases
import Lean.Meta.Tactic.Grind.Injection
import Lean.Meta.Tactic.Grind.Core
import Lean.Meta.Tactic.Grind.Canon
import Lean.Meta.Tactic.Grind.MarkNestedProofs
import Lean.Meta.Tactic.Grind.Inv
import Lean.Meta.Tactic.Grind.Proof
import Lean.Meta.Tactic.Grind.Propagate
import Lean.Meta.Tactic.Grind.PP
import Lean.Meta.Tactic.Grind.Simp
import Lean.Meta.Tactic.Grind.Ctor
import Lean.Meta.Tactic.Grind.Parser
import Lean.Meta.Tactic.Grind.EMatchTheorem

namespace Lean

/-! Trace options for `grind` users -/
builtin_initialize registerTraceClass `grind
builtin_initialize registerTraceClass `grind.assert
builtin_initialize registerTraceClass `grind.eqc
builtin_initialize registerTraceClass `grind.internalize
builtin_initialize registerTraceClass `grind.ematch
builtin_initialize registerTraceClass `grind.ematch.instance
builtin_initialize registerTraceClass `grind.issues
builtin_initialize registerTraceClass `grind.simp

/-! Trace options for `grind` developers -/
builtin_initialize registerTraceClass `grind.debug
builtin_initialize registerTraceClass `grind.debug.proofs
builtin_initialize registerTraceClass `grind.debug.congr
builtin_initialize registerTraceClass `grind.debug.pre
builtin_initialize registerTraceClass `grind.debug.proof
builtin_initialize registerTraceClass `grind.debug.proj

end Lean
