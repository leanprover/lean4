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


def blastClz (aig : AIG α) (target : AIG.RefVec aig w) :
    AIG.RefVecEntry α w :=
  go aig target (w - 1)
where
  go (aig : AIG α) (x : AIG.RefVec aig w) (curr : Nat) :
    AIG.RefVecEntry α w :=
    -- if curr = 0 then BitVec.ofNat w w
    if curr = 0 then
      -- return w
      blastConst aig w
    else
      -- cond = x.getLsbD n
      let res := (BVPred.blastGetLsbD aig ⟨x, curr⟩)
      let aig := res.aig
      let cond := res.ref
      have := AIG.LawfulOperator.le_size (f := BVPred.blastGetLsbD) ..
      -- lhs = BitVec.ofNat w (w - 1 - curr)
      let res := blastConst aig (w - 1 - curr)
      let aig := res.aig
      let lhs := res.vec
      have := AIG.LawfulVecOperator.le_size (f := blastConst) ..
      let cond := cond.cast this
      -- rhs = clzAuxRec x (curr - 1)
      let res := go x (curr - 1)
      let aig := res.aig
      let rhs := res.ref
      -- return ite cond lhs rhs
      let res := AIG.RefVec.ite aig ⟨cond, lhs, rhs⟩
      res
  termination_by curr

end bitblast
end BVExpr

end Std.Tactic.BVDecide
