/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luisa Cicolini
-/
prelude
import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.GetLsbD
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Eq
import Std.Sat.AIG
import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Sub
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Eq
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Ult
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.ZeroExtend
import Std.Sat.AIG.If

/-!
This module contains the implementation of a bitblaster for `BitVec.clz`.
-/

namespace Std.Tactic.BVDecide

open Std.Sat

namespace BVExpr
namespace bitblast

variable [Hashable α] [DecidableEq α]

-- def clzAuxRec {w : Nat} (x : BitVec w) (n : Nat) : BitVec w :=
--   if hn : n = 0 then BitVec.ofNat w w
--     else if x.getLsbD n then BitVec.ofNat w (w - 1 - n)
--       else clzAuxRec x (n - 1)


def blastClz (aig : AIG α) (x : AIG.RefVec aig w) :
    AIG.RefVecEntry α w :=
  let res := blastConst aig (w - 1)
  let aig := res.aig
  let acc := res.vec
  have := AIG.LawfulVecOperator.le_size (f := blastConst) ..
  have x := x.cast this
  go aig x 0 acc
where
  go (aig : AIG α) (x : AIG.RefVec aig w) (curr : Nat) (acc : AIG.RefVec aig w) :=
    if curr < w then
      -- w - curr - 1
      let res := blastConst aig (w := w) (w - 1 - curr)
      let aig  := res.aig
      let lhs := res.vec
      have := AIG.LawfulVecOperator.le_size (f := blastConst) ..
      let x : AIG.RefVec aig w := x.cast this
      let acc : AIG.RefVec aig w := acc.cast this
      -- x.getLsbD (curr)
      let res := BVPred.blastGetLsbD aig ⟨x, curr⟩
      let aig := res.aig
      let lsb := res.ref
      have := AIG.LawfulOperator.le_size (f := BVPred.blastGetLsbD) ..
      let x : AIG.RefVec aig w := x.cast this
      let acc : AIG.RefVec aig w := acc.cast this
      let lhs := lhs.cast this
      -- ite x.getLsbD (curr)
      let res := AIG.RefVec.ite aig ⟨lsb, lhs, acc⟩
      let aig := res.aig
      let ite := res.vec
      have := AIG.LawfulVecOperator.le_size (f := AIG.RefVec.ite) ..
      let x : AIG.RefVec aig w := x.cast this
      let acc : AIG.RefVec aig w := acc.cast this
      let lhs := lhs.cast this
      let lsb := lsb.cast this
      go aig x (curr + 1) acc
    else
      ⟨aig, acc⟩
  termination_by w - 1 - curr

end bitblast
end BVExpr

end Std.Tactic.BVDecide
