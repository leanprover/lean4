/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Util.Trace
import Lean.Meta.Tactic.Grind.Arith.Cutsat.DvdCnstr
import Lean.Meta.Tactic.Grind.Arith.Cutsat.RelCnstr
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Inv
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Proof
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Types
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Var

namespace Lean

builtin_initialize registerTraceClass `grind.cutsat
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

end Lean
