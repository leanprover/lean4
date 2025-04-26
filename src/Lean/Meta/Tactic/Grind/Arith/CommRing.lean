/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Util.Trace
import Lean.Meta.Tactic.Grind.Arith.CommRing.Poly
import Lean.Meta.Tactic.Grind.Arith.CommRing.Types
import Lean.Meta.Tactic.Grind.Arith.CommRing.RingId
import Lean.Meta.Tactic.Grind.Arith.CommRing.Internalize
import Lean.Meta.Tactic.Grind.Arith.CommRing.ToExpr
import Lean.Meta.Tactic.Grind.Arith.CommRing.Var
import Lean.Meta.Tactic.Grind.Arith.CommRing.Reify
import Lean.Meta.Tactic.Grind.Arith.CommRing.EqCnstr
import Lean.Meta.Tactic.Grind.Arith.CommRing.Proof
import Lean.Meta.Tactic.Grind.Arith.CommRing.DenoteExpr

namespace Lean

builtin_initialize registerTraceClass `grind.ring
builtin_initialize registerTraceClass `grind.ring.internalize
builtin_initialize registerTraceClass `grind.ring.assert
builtin_initialize registerTraceClass `grind.ring.assert.unsat (inherited := true)
builtin_initialize registerTraceClass `grind.ring.assert.trivial (inherited := true)
builtin_initialize registerTraceClass `grind.ring.assert.queue (inherited := true)
builtin_initialize registerTraceClass `grind.ring.assert.basis (inherited := true)
builtin_initialize registerTraceClass `grind.ring.assert.discard (inherited := true)
builtin_initialize registerTraceClass `grind.ring.simp
builtin_initialize registerTraceClass `grind.ring.superpose

builtin_initialize registerTraceClass `grind.debug.ring.simp
builtin_initialize registerTraceClass `grind.debug.ring.proof

end Lean
