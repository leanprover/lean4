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
  go aig x w acc
where
  go (aig : AIG α) (x : AIG.RefVec aig w) (fuel : Nat) (acc : AIG.RefVec aig w) :=
    if hf : 0 < fuel then
      let one : AIG.RefVec aig w := blastConst aig (w := w) 1

      -- ite x = 0, acc, acc


      -- acc := acc + 1
      let res : AIG.RefVecEntry α w := blastAdd aig ⟨acc, one⟩
      let aig := res.aig
      let add : AIG.RefVec aig w := res.vec
      have := AIG.LawfulVecOperator.le_size (f := blastAdd) ..
      let one : AIG.RefVec aig w := one.cast this
      let x := x.cast this

      -- ite x recCall acc

      -- sub := x - 1
      let res : AIG.RefVecEntry α w := blastSub aig ⟨x, one⟩
      let aig := res.aig
      let sub : AIG.RefVec aig w := res.vec
      have := AIG.LawfulVecOperator.le_size (f := blastSub) ..
      let x := x.cast this
      let add : AIG.RefVec aig w := acc.cast this

      -- x :=& sub
      let res : AIG.RefVecEntry α w := AIG.RefVec.zip aig ⟨x, sub⟩ AIG.mkAndCached
      let aig := res.aig
      let x : AIG.RefVec aig w  := res.vec
      have := AIG.RefVec.zip_le_size ..
      let acc := acc.cast this

      go aig x (fuel - 1) acc
    else
      ⟨aig, acc⟩
  termination_by fuel

namespace blastPopCnt

end blastPopCnt

theorem blastPopCnt.go_le_size (aig : AIG α) (fuel : Nat) (acc : AIG.RefVec aig w)
    (xc : AIG.RefVec aig w) :
    aig.decls.size ≤ (go aig xc fuel acc).aig.decls.size := by
  unfold go
  dsimp only
  split
  · simp [AIG.RefVec.zip_le_size]
    sorry
  · simp
  -- dsimp only
  -- split
  -- · refine Nat.le_trans ?_ (by apply go_le_size)x
  --   sorry
  -- · simp
termination_by fuel

theorem blastPopCnt.go_decl_eq (aig : AIG α) (fuel : Nat) (acc : AIG.RefVec aig w)
    (xc : AIG.RefVec aig w) :
    ∀ (idx : Nat) h1 h2,
        (go aig xc fuel acc).aig.decls[idx]'h1 = aig.decls[idx]'h2 := by
  generalize hgo : go aig xc fuel acc = res
  unfold go at hgo
  dsimp only at hgo
  split at hgo
  · rw [← hgo]
    intros
    simp [AIG.RefVec.zip_le_size]
    rw [AIG.LawfulVecOperator.decl_eq (f := AIG.RefVec.zip)]
    sorry
    -- rw [blastPopCnt.go_decl_eq, AIG.LawfulVecOperator.decl_eq (f := AIG.RefVec.ite)]
    -- apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := AIG.RefVec.ite)
    -- assumption
  · simp [← hgo]
termination_by w - curr

instance : AIG.LawfulVecOperator α AIG.RefVec blastPopCnt where
  le_size := by
    intros
    unfold blastPopCnt
    dsimp only
    apply blastPopCnt.go_le_size
  decl_eq := by
    intros
    unfold blastPopCnt
    dsimp only
    apply blastPopCnt.go_decl_eq

end bitblast
end BVExpr

end Std.Tactic.BVDecide
