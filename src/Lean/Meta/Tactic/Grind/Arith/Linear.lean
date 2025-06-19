/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Arith.Linear.Types
import Lean.Meta.Tactic.Grind.Arith.Linear.Util
import Lean.Meta.Tactic.Grind.Arith.Linear.Var
import Lean.Meta.Tactic.Grind.Arith.Linear.StructId
import Lean.Meta.Tactic.Grind.Arith.Linear.IneqCnstr
import Lean.Meta.Tactic.Grind.Arith.Linear.Reify
import Lean.Meta.Tactic.Grind.Arith.Linear.DenoteExpr
import Lean.Meta.Tactic.Grind.Arith.Linear.ToExpr
import Lean.Meta.Tactic.Grind.Arith.Linear.Proof
import Lean.Meta.Tactic.Grind.Arith.Linear.SearchM
import Lean.Meta.Tactic.Grind.Arith.Linear.Search
import Lean.Meta.Tactic.Grind.Arith.Linear.PropagateEq
import Lean.Meta.Tactic.Grind.Arith.Linear.Internalize
import Lean.Meta.Tactic.Grind.Arith.Linear.Model
import Lean.Meta.Tactic.Grind.Arith.Linear.PP
import Lean.Meta.Tactic.Grind.Arith.Linear.MBTC

namespace Lean

builtin_initialize registerTraceClass `grind.linarith
builtin_initialize registerTraceClass `grind.linarith.internalize
builtin_initialize registerTraceClass `grind.linarith.assert
builtin_initialize registerTraceClass `grind.linarith.model
builtin_initialize registerTraceClass `grind.linarith.assert.unsat (inherited := true)
builtin_initialize registerTraceClass `grind.linarith.assert.trivial (inherited := true)
builtin_initialize registerTraceClass `grind.linarith.assert.store (inherited := true)
builtin_initialize registerTraceClass `grind.linarith.assert.ignored (inherited := true)

builtin_initialize registerTraceClass `grind.debug.linarith.search
builtin_initialize registerTraceClass `grind.debug.linarith.search.conflict (inherited := true)
builtin_initialize registerTraceClass `grind.debug.linarith.search.assign (inherited := true)
builtin_initialize registerTraceClass `grind.debug.linarith.search.split (inherited := true)
builtin_initialize registerTraceClass `grind.debug.linarith.search.backtrack (inherited := true)
builtin_initialize registerTraceClass `grind.debug.linarith.subst

end Lean
