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
import Lean.Meta.Tactic.Grind.Arith.Cutsat.DivMod

namespace Lean

builtin_initialize registerTraceClass `grind.cutsat
builtin_initialize registerTraceClass `grind.cutsat.model
builtin_initialize registerTraceClass `grind.cutsat.subst
builtin_initialize registerTraceClass `grind.cutsat.eq
builtin_initialize registerTraceClass `grind.cutsat.eq.unsat (inherited := true)
builtin_initialize registerTraceClass `grind.cutsat.eq.trivial (inherited := true)
builtin_initialize registerTraceClass `grind.cutsat.assert
builtin_initialize registerTraceClass `grind.cutsat.assert.dvd
builtin_initialize registerTraceClass `grind.cutsat.dvd
builtin_initialize registerTraceClass `grind.cutsat.dvd.update (inherited := true)
builtin_initialize registerTraceClass `grind.cutsat.dvd.unsat (inherited := true)
builtin_initialize registerTraceClass `grind.cutsat.dvd.trivial (inherited := true)
builtin_initialize registerTraceClass `grind.cutsat.dvd.solve (inherited := true)
builtin_initialize registerTraceClass `grind.cutsat.dvd.solve.combine (inherited := true)
builtin_initialize registerTraceClass `grind.cutsat.dvd.solve.elim (inherited := true)
builtin_initialize registerTraceClass `grind.cutsat.internalize
builtin_initialize registerTraceClass `grind.cutsat.internalize.term (inherited := true)

builtin_initialize registerTraceClass `grind.cutsat.assert.le
builtin_initialize registerTraceClass `grind.cutsat.le
builtin_initialize registerTraceClass `grind.cutsat.le.unsat (inherited := true)
builtin_initialize registerTraceClass `grind.cutsat.le.trivial (inherited := true)
builtin_initialize registerTraceClass `grind.cutsat.le.lower (inherited := true)
builtin_initialize registerTraceClass `grind.cutsat.le.upper (inherited := true)
builtin_initialize registerTraceClass `grind.cutsat.assign
builtin_initialize registerTraceClass `grind.cutsat.conflict

builtin_initialize registerTraceClass `grind.cutsat.diseq
builtin_initialize registerTraceClass `grind.cutsat.diseq.trivial (inherited := true)

builtin_initialize registerTraceClass `grind.debug.cutsat.eq
builtin_initialize registerTraceClass `grind.debug.cutsat.diseq
builtin_initialize registerTraceClass `grind.debug.cutsat.diseq.split
builtin_initialize registerTraceClass `grind.debug.cutsat.backtrack
builtin_initialize registerTraceClass `grind.debug.cutsat.search
builtin_initialize registerTraceClass `grind.debug.cutsat.cooper
builtin_initialize registerTraceClass `grind.debug.cutsat.conflict
builtin_initialize registerTraceClass `grind.debug.cutsat.assign
builtin_initialize registerTraceClass `grind.debug.cutsat.subst

end Lean
