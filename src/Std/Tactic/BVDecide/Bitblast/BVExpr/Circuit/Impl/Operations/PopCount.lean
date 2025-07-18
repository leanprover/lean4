/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luisa Cicolini, Siddharth Bhat, Henrik Böving
-/
prelude
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Const
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Sub
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Eq
import Std.Sat.AIG.If

/-!
This module contains the implementation of a bitblaster for `BitVec.popCount`.
-/

namespace Std.Tactic.BVDecide

open Std.Sat

variable [Hashable α] [DecidableEq α]

namespace BVExpr
namespace bitblast

def blastPopCount (aig : AIG α) (x : AIG.RefVec aig w) :
    AIG.RefVecEntry α w :=
  let wconst : AIG.RefVec aig w := blastConst aig (w := w) w
  go aig x 0 wconst
where
  go (aig : AIG α) (x : AIG.RefVec aig w) (curr : Nat) (acc : AIG.RefVec aig w) :=
    if hf : curr < w then
      -- create curr constant node
      let currConst : AIG.RefVec aig w := blastConst aig (w := w) curr
      let zero : AIG.RefVec aig w := blastConst aig (w := w) 0
      -- create node x = 0
      let res := BVPred.mkEq aig ⟨x, zero⟩
      let aig := res.aig
      let cond := res.ref
      have := AIG.LawfulOperator.le_size (f := BVPred.mkEq) ..
      let currConst := currConst.cast this
      let x := x.cast this
      let acc := acc.cast this
      -- ite (x & x - 1) then acc else cnt
      let res := AIG.RefVec.ite aig ⟨cond, currConst, acc⟩
      let aig := res.aig
      let acc := res.vec
      have := AIG.LawfulVecOperator.le_size (f := AIG.RefVec.ite) ..
      let x := x.cast this
      -- sub := x - 1
      let one : AIG.RefVec aig w := blastConst aig (w := w) 1
      let res : AIG.RefVecEntry α w := blastSub aig ⟨x, one⟩
      let aig := res.aig
      let sub : AIG.RefVec aig w := res.vec
      have := AIG.LawfulVecOperator.le_size (f := blastSub) ..
      let x := x.cast this
      let acc := acc.cast this
      -- x :=& sub
      let res : AIG.RefVecEntry α w := AIG.RefVec.zip aig ⟨x, sub⟩ AIG.mkAndCached
      let aig := res.aig
      let x := res.vec
      have := AIG.RefVec.zip_le_size ..
      let acc := acc.cast this
      go aig x (curr + 1) acc
    else
      ⟨aig, acc⟩
  termination_by (w - curr)

namespace blastPopCount

end blastPopCount

theorem blastPopCount.go_le_size (aig : AIG α) (curr : Nat) (acc : AIG.RefVec aig w)
    (xc : AIG.RefVec aig w) :
    aig.decls.size ≤ (go aig xc curr acc).aig.decls.size := by
  unfold go
  dsimp only
  split
  · refine Nat.le_trans ?_ (by apply go_le_size)
    refine
      AIG.RefVec.zip_le_size_of_le_aig_size
        (blastSub
            (AIG.RefVec.ite (BVPred.mkEq aig { lhs := xc, rhs := blastConst aig 0 }).aig
                { discr := (BVPred.mkEq aig { lhs := xc, rhs := blastConst aig 0 }).ref,
                  lhs := (blastConst aig ↑curr).cast (go._proof_1 aig xc),
                  rhs := acc.cast (go._proof_1 aig xc) }).aig
            {
              lhs :=
                (xc.cast (go._proof_1 aig xc)).cast
                  (go._proof_2 aig xc curr acc (go._proof_1 aig xc)),
              rhs :=
                blastConst
                  (AIG.RefVec.ite (BVPred.mkEq aig { lhs := xc, rhs := blastConst aig 0 }).aig
                      { discr := (BVPred.mkEq aig { lhs := xc, rhs := blastConst aig 0 }).ref,
                        lhs := (blastConst aig ↑curr).cast (go._proof_1 aig xc),
                        rhs := acc.cast (go._proof_1 aig xc) }).aig
                  1 }).aig
        {
          lhs :=
            ((xc.cast (go._proof_1 aig xc)).cast
                  (go._proof_2 aig xc curr acc (go._proof_1 aig xc))).cast
              (go._proof_3 aig xc curr acc (go._proof_1 aig xc)
                (go._proof_2 aig xc curr acc (go._proof_1 aig xc))),
          rhs :=
            (blastSub
                (AIG.RefVec.ite (BVPred.mkEq aig { lhs := xc, rhs := blastConst aig 0 }).aig
                    { discr := (BVPred.mkEq aig { lhs := xc, rhs := blastConst aig 0 }).ref,
                      lhs := (blastConst aig ↑curr).cast (go._proof_1 aig xc),
                      rhs := acc.cast (go._proof_1 aig xc) }).aig
                {
                  lhs :=
                    (xc.cast (go._proof_1 aig xc)).cast
                      (go._proof_2 aig xc curr acc (go._proof_1 aig xc)),
                  rhs :=
                    blastConst
                      (AIG.RefVec.ite (BVPred.mkEq aig { lhs := xc, rhs := blastConst aig 0 }).aig
                          { discr := (BVPred.mkEq aig { lhs := xc, rhs := blastConst aig 0 }).ref,
                            lhs := (blastConst aig ↑curr).cast (go._proof_1 aig xc),
                            rhs := acc.cast (go._proof_1 aig xc) }).aig
                      1 }).vec }
        AIG.mkAndCached ?_
    simp
    apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := blastSub)
    apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := AIG.RefVec.ite)
    unfold BVPred.mkEq
    refine
      AIG.RefVec.fold_le_size_of_le_aig_size
        (AIG.RefVec.zip aig { lhs := xc, rhs := blastConst aig 0#w } AIG.mkBEqCached).aig
        (AIG.RefVec.zip aig { lhs := xc, rhs := blastConst aig 0#w } AIG.mkBEqCached).vec
        AIG.mkAndCached ?_
    exact AIG.RefVec.zip_le_size aig { lhs := xc, rhs := blastConst aig 0#w } AIG.mkBEqCached
  · simp

theorem blastPopCount.go_decl_eq (aig : AIG α) (curr : Nat) (acc : AIG.RefVec aig w)
    (xc : AIG.RefVec aig w) :
    ∀ (idx : Nat) h1 h2,
        (go aig xc curr acc).aig.decls[idx]'h1 = aig.decls[idx]'h2 := by
  generalize hgo : go aig xc curr acc = res
  unfold go at hgo
  dsimp only at hgo
  split at hgo
  · rw [← hgo]
    intros
    rw [blastPopCount.go_decl_eq, AIG.RefVec.zip_decl_eq, AIG.LawfulVecOperator.decl_eq (f := blastSub)]
    · rw [AIG.LawfulVecOperator.decl_eq (f := AIG.RefVec.ite)]
      · apply AIG.LawfulOperator.decl_eq (f := BVPred.mkEq)
      · apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := BVPred.mkEq)
        (expose_names; exact h2)
      · apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := AIG.RefVec.ite)
        apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := BVPred.mkEq)
        (expose_names; exact h2)
    · apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastSub)
      apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := AIG.RefVec.ite)
      unfold BVPred.mkEq
      refine
        AIG.RefVec.fold_lt_size_of_lt_aig_size
          (AIG.RefVec.zip aig { lhs := xc, rhs := blastConst aig 0 } AIG.mkBEqCached).aig
          (AIG.RefVec.zip aig { lhs := xc, rhs := blastConst aig 0 } AIG.mkBEqCached).vec
          AIG.mkAndCached ?_
      (expose_names;
        exact
          AIG.RefVec.zip_lt_size_of_lt_aig_size aig { lhs := xc, rhs := blastConst aig 0 }
            AIG.mkBEqCached h2)
    · refine
      AIG.RefVec.zip_lt_size_of_lt_aig_size
        (blastSub
            (AIG.RefVec.ite (BVPred.mkEq aig { lhs := xc, rhs := blastConst aig 0 }).aig
                { discr := (BVPred.mkEq aig { lhs := xc, rhs := blastConst aig 0 }).ref,
                  lhs := (blastConst aig ↑curr).cast (go._proof_1 aig xc),
                  rhs := acc.cast (go._proof_1 aig xc) }).aig
            {
              lhs :=
                (xc.cast (go._proof_1 aig xc)).cast
                  (go._proof_2 aig xc curr acc (go._proof_1 aig xc)),
              rhs :=
                blastConst
                  (AIG.RefVec.ite (BVPred.mkEq aig { lhs := xc, rhs := blastConst aig 0 }).aig
                      { discr := (BVPred.mkEq aig { lhs := xc, rhs := blastConst aig 0 }).ref,
                        lhs := (blastConst aig ↑curr).cast (go._proof_1 aig xc),
                        rhs := acc.cast (go._proof_1 aig xc) }).aig
                  1 }).aig
        {
          lhs :=
            ((xc.cast (go._proof_1 aig xc)).cast
                  (go._proof_2 aig xc curr acc (go._proof_1 aig xc))).cast
              (go._proof_3 aig xc curr acc (go._proof_1 aig xc)
                (go._proof_2 aig xc curr acc (go._proof_1 aig xc))),
          rhs :=
            (blastSub
                (AIG.RefVec.ite (BVPred.mkEq aig { lhs := xc, rhs := blastConst aig 0 }).aig
                    { discr := (BVPred.mkEq aig { lhs := xc, rhs := blastConst aig 0 }).ref,
                      lhs := (blastConst aig ↑curr).cast (go._proof_1 aig xc),
                      rhs := acc.cast (go._proof_1 aig xc) }).aig
                {
                  lhs :=
                    (xc.cast (go._proof_1 aig xc)).cast
                      (go._proof_2 aig xc curr acc (go._proof_1 aig xc)),
                  rhs :=
                    blastConst
                      (AIG.RefVec.ite (BVPred.mkEq aig { lhs := xc, rhs := blastConst aig 0 }).aig
                          { discr := (BVPred.mkEq aig { lhs := xc, rhs := blastConst aig 0 }).ref,
                            lhs := (blastConst aig ↑curr).cast (go._proof_1 aig xc),
                            rhs := acc.cast (go._proof_1 aig xc) }).aig
                      1 }).vec }
        AIG.mkAndCached ?_
      apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastSub)
      apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := AIG.RefVec.ite)
      unfold BVPred.mkEq
      refine
        AIG.RefVec.fold_lt_size_of_lt_aig_size
          (AIG.RefVec.zip aig { lhs := xc, rhs := blastConst aig 0 } AIG.mkBEqCached).aig
          (AIG.RefVec.zip aig { lhs := xc, rhs := blastConst aig 0 } AIG.mkBEqCached).vec
          AIG.mkAndCached ?_
      (expose_names;
        exact
          AIG.RefVec.zip_lt_size_of_lt_aig_size aig { lhs := xc, rhs := blastConst aig 0 }
            AIG.mkBEqCached h2)
  · simp [← hgo]
termination_by w - curr

instance : AIG.LawfulVecOperator α AIG.RefVec blastPopCount where
  le_size := by
    intros
    unfold blastPopCount
    dsimp only
    apply blastPopCount.go_le_size
  decl_eq := by
    intros
    unfold blastPopCount
    dsimp only
    apply blastPopCount.go_decl_eq

end bitblast
end BVExpr

end Std.Tactic.BVDecide
