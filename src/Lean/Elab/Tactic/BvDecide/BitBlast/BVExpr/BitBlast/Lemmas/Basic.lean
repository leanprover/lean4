/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Sat.AIG.Basic
import Lean.Elab.Tactic.BvDecide.BitBlast.BVExpr.Basic

/-!
This module contains basic infrastructure for converting between variable assignments of `BVExpr`
and `AIG`. This is necessary because `BVExpr` needs to use a list and indices into said list instead
of a function due to the way that it is used in `bv_decide`.
-/

namespace Lean.Elab.Tactic.BvDecide

namespace BVExpr

def Assignment.toAIGAssignment (assign : Assignment) : BVBit → Bool :=
  fun bit => (assign.getD bit.var).bv.getLsb bit.idx

@[simp]
theorem Assignment.toAIGAssignment_apply (assign : Assignment) (bit : BVBit) :
    assign.toAIGAssignment bit = (assign.getD bit.var).bv.getLsb bit.idx := by
  rfl

end BVExpr

end Lean.Elab.Tactic.BvDecide
