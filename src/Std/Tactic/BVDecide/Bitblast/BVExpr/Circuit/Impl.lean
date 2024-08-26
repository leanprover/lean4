/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Pred
import Std.Tactic.BVDecide.Bitblast.BoolExpr.Circuit

/-!
This module contains the implementation of a bitblaster for general `BitVec` problems with boolean
substructure (`BVLogicalExpr`). It is the main entrypoint into the bitblasting framework.
-/

namespace Std.Tactic.BVDecide

open Std.Sat

namespace BVLogicalExpr

def bitblast (expr : BVLogicalExpr) : AIG.Entrypoint BVBit :=
  ofBoolExprCached expr BVPred.bitblast

end BVLogicalExpr

end Std.Tactic.BVDecide
