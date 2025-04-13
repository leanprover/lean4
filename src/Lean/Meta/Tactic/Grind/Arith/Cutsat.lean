/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Util.Trace
import Lean.Meta.Tactic.Grind.Arith.Cutsat.DvdCnstr
import Lean.Meta.Tactic.Grind.Arith.Cutsat.LeCnstr
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Search
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Inv
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Proof
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Types
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Var
import Lean.Meta.Tactic.Grind.Arith.Cutsat.EqCnstr
import Lean.Meta.Tactic.Grind.Arith.Cutsat.SearchM
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Model
import Lean.Meta.Tactic.Grind.Arith.Cutsat.MBTC

namespace Lean

builtin_initialize registerTraceClass `grind.cutsat
builtin_initialize registerTraceClass `grind.cutsat.model
builtin_initialize registerTraceClass `grind.cutsat.assert
builtin_initialize registerTraceClass `grind.cutsat.assert.trivial
builtin_initialize registerTraceClass `grind.cutsat.assert.unsat
builtin_initialize registerTraceClass `grind.cutsat.assert.store

builtin_initialize registerTraceClass `grind.debug.cutsat.subst
builtin_initialize registerTraceClass `grind.debug.cutsat.search
builtin_initialize registerTraceClass `grind.debug.cutsat.search.split (inherited := true)
builtin_initialize registerTraceClass `grind.debug.cutsat.search.assign (inherited := true)
builtin_initialize registerTraceClass `grind.debug.cutsat.search.conflict (inherited := true)
builtin_initialize registerTraceClass `grind.debug.cutsat.search.backtrack (inherited := true)
builtin_initialize registerTraceClass `grind.debug.cutsat.internalize

end Lean
