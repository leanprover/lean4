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

namespace Lean

builtin_initialize registerTraceClass `grind.ring
builtin_initialize registerTraceClass `grind.ring.internalize

end Lean
