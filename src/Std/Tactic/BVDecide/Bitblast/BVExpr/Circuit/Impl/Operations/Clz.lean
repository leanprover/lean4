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

def blastClz (aig : AIG α) (target : AIG.RefVec aig w) :
    AIG.RefVecEntry α w :=
  go aig target (w - 1)
where
  go (aig : AIG α) (x : AIG.RefVec aig w) (curr : Nat) :
    AIG.ExtendingRefVecEntry aig w :=
  if hc : curr = 0 then
    -- getLsbD 0
    let res := (BVPred.blastGetLsbD aig ⟨x, 0⟩)
    let aig := res.aig
    let lsb := res.ref
    -- 0
    let res := blastConst aig 0
    let aig := res.aig
    let zero := res.vec
    have := AIG.LawfulVecOperator.le_size (f := blastConst) ..
    let lsb := lsb.cast this
    -- 1
    let res := blastConst aig 1
    let aig := res.aig
    let one := res.vec
    have := AIG.LawfulVecOperator.le_size (f := blastConst) ..
    let lsb := lsb.cast this
    let zero := zero.cast this
    -- ite (getLsbD 0) 0 1
    let res := AIG.RefVec.ite aig ⟨lsb, zero, one⟩
    let aig := res.aig
    let ite := res.vec
    have := AIG.LawfulVecOperator.le_size (f := AIG.RefVec.ite) (input := ⟨lsb, zero, one⟩) ..
    let lsb := lsb.cast this
    let zero := zero.cast this
    let one := one.cast this
    have := AIG.LawfulVecOperator.le_size_of_le_aig_size (f := AIG.RefVec.ite) (input := ⟨lsb, zero, one⟩)  (x := sorry) (by omega)
    ⟨res, by sorry ⟩
  else
    -- getLsbD curr
    let res := (BVPred.blastGetLsbD aig ⟨x, curr⟩)
    let aig := res.aig
    let lsb := res.ref
    have := AIG.LawfulOperator.le_size (f := BVPred.blastGetLsbD) ..
    let x := x.cast this
    -- 0
    let res := blastConst aig 0
    let aig := res.aig
    let zero := res.vec
    have := AIG.LawfulVecOperator.le_size (f := blastConst) ..
    let lsb : aig.Ref := lsb.cast this
    let x := x.cast this
    -- 1
    let res := blastConst aig 1
    let aig := res.aig
    let one : AIG.RefVec aig w := res.vec
    have := AIG.LawfulVecOperator.le_size (f := blastConst) ..
    let lsb : aig.Ref := lsb.cast this
    let x := x.cast this
    let zero := zero.cast this
    -- clzAuxRec x curr'
    let ⟨res,proof⟩ := go aig x (curr - 1)
    let aig := res.aig
    let clzRec := res.vec
    let lsb : aig.Ref := lsb.cast proof
    let x := x.cast proof
    let zero := zero.cast proof
    let one : AIG.RefVec aig w := one.cast proof
    -- 1 + clzAuxRec x curr'
    let res := blastAdd aig ⟨one, clzRec⟩
    let aig := res.aig
    let add := res.vec
    have := AIG.LawfulVecOperator.le_size (f := blastAdd) ..
    let lsb : aig.Ref := lsb.cast this
    let x := x.cast this
    let zero := zero.cast this
    let one := one.cast (by (expose_names; exact Nat.le_refl aig_6.decls.size))
    let clzRec := clzRec.cast (by (expose_names; exact Nat.le_refl res_4.aig.decls.size))
    let ite := AIG.RefVec.ite aig ⟨lsb, zero, add⟩
    ⟨ite, by sorry⟩
  termination_by curr

end bitblast
end BVExpr

end Std.Tactic.BVDecide
