/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luisa Cicolini, Siddharth Bhat, Henrik Böving
-/
prelude
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Const
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Sub
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Expr
import Std.Sat.AIG.If

/-!
This module contains the implementation of a bitblaster for `BitVec.clz`.
-/

namespace Std.Tactic.BVDecide

open Std.Sat

variable [Hashable α] [DecidableEq α]

namespace BVExpr
namespace bitblast

def blastPopCnt (aig : AIG α) (x : AIG.RefVec aig w) :
    AIG.RefVecEntry α w :=
  let acc := blastConst aig (w := w) 0
  go aig x 0 acc
where
  go (aig : AIG α) (x : AIG.RefVec aig w) (fuel : Nat) (acc : AIG.RefVec aig w) :=
    if hf : fuel < w then
      let one : AIG.RefVec aig w := blastConst aig (w := w) 1
      -- acc := acc + 1
      let res : AIG.RefVecEntry α w := blastAdd aig ⟨acc, one⟩
      let aig := res.aig
      let acc : AIG.RefVec aig w := res.vec
      have := AIG.LawfulVecOperator.le_size (f := blastAdd) ..
      let one : AIG.RefVec aig w := one.cast this
      let x := x.cast this
      -- sub := x - 1
      let res : AIG.RefVecEntry α w := blastSub aig ⟨x, one⟩
      let aig := res.aig
      let sub : AIG.RefVec aig w := res.vec
      have := AIG.LawfulVecOperator.le_size (f := blastSub) ..
      let x := x.cast this
      let acc := acc.cast this
      -- x :=& sub
      let res : AIG.RefVecEntry α w := AIG.RefVec.zip aig ⟨x, sub⟩ AIG.mkAndCached
      let aig := res.aig
      let x : AIG.RefVec aig w  := res.vec
      have := AIG.RefVec.zip_le_size ..
      let acc := acc.cast this
      go aig x (fuel + 1) acc
    else
      ⟨aig, acc⟩
  termination_by (w - fuel)

namespace blastPopCnt

end blastPopCnt


end bitblast
end BVExpr

end Std.Tactic.BVDecide
