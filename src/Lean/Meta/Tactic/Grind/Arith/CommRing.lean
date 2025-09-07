/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Util.Trace
public import Lean.Meta.Tactic.Grind.Arith.CommRing.Poly
public import Lean.Meta.Tactic.Grind.Arith.CommRing.Types
public import Lean.Meta.Tactic.Grind.Arith.CommRing.RingId
public import Lean.Meta.Tactic.Grind.Arith.CommRing.Internalize
public import Lean.Meta.Tactic.Grind.Arith.CommRing.ToExpr
public import Lean.Meta.Tactic.Grind.Arith.CommRing.RingM
public import Lean.Meta.Tactic.Grind.Arith.CommRing.SemiringM
public import Lean.Meta.Tactic.Grind.Arith.CommRing.Functions
public import Lean.Meta.Tactic.Grind.Arith.CommRing.Reify
public import Lean.Meta.Tactic.Grind.Arith.CommRing.EqCnstr
public import Lean.Meta.Tactic.Grind.Arith.CommRing.Proof
public import Lean.Meta.Tactic.Grind.Arith.CommRing.DenoteExpr
public import Lean.Meta.Tactic.Grind.Arith.CommRing.Inv
public import Lean.Meta.Tactic.Grind.Arith.CommRing.PP
public import Lean.Meta.Tactic.Grind.Arith.CommRing.VarRename

public section

namespace Lean

builtin_initialize registerTraceClass `grind.ring
builtin_initialize registerTraceClass `grind.ring.internalize
builtin_initialize registerTraceClass `grind.ring.assert
builtin_initialize registerTraceClass `grind.ring.assert.unsat (inherited := true)
builtin_initialize registerTraceClass `grind.ring.assert.trivial (inherited := true)
builtin_initialize registerTraceClass `grind.ring.assert.queue (inherited := true)
builtin_initialize registerTraceClass `grind.ring.assert.basis (inherited := true)
builtin_initialize registerTraceClass `grind.ring.assert.store (inherited := true)
builtin_initialize registerTraceClass `grind.ring.simp
builtin_initialize registerTraceClass `grind.ring.superpose
builtin_initialize registerTraceClass `grind.ring.impEq

builtin_initialize registerTraceClass `grind.debug.ring.simp
builtin_initialize registerTraceClass `grind.debug.ring.proof
builtin_initialize registerTraceClass `grind.debug.ring.check
builtin_initialize registerTraceClass `grind.debug.ring.impEq
builtin_initialize registerTraceClass `grind.debug.ring.simpBasis
builtin_initialize registerTraceClass `grind.debug.ring.basis
builtin_initialize registerTraceClass `grind.debug.ring.rabinowitsch

end Lean
