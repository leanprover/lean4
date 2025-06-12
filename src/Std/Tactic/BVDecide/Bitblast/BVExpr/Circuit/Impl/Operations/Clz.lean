/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luisa Cicolini, Siddharth Bhat
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

variable [Hashable α] [DecidableEq α]

namespace BVExpr
namespace bitblast

def blastClz (aig : AIG α) (x : AIG.RefVec aig w) :
    AIG.RefVecEntry α w :=
  let wconst := blastConst aig w
  go aig x 0 wconst
where
  go (aig : AIG α) (x : AIG.RefVec aig w) (curr : Nat) (acc : AIG.RefVec aig w) :=
    if hc : curr < w then
      -- w - curr - 1
      let lhs := blastConst aig (w := w) (w - 1 - curr)
      let res := AIG.RefVec.ite aig ⟨x.get curr hc, lhs, acc⟩
      let aig := res.aig
      let acc := res.vec
      have := by apply AIG.LawfulVecOperator.le_size (f := AIG.RefVec.ite)
      let x : AIG.RefVec aig w := x.cast this
      go aig x (curr + 1) acc
    else
      ⟨aig, acc⟩
  termination_by w - curr

namespace blastClz

end blastClz

theorem blastClz.go_le_size (aig : AIG α) (curr : Nat) (acc : AIG.RefVec aig w)
    (xc : AIG.RefVec aig w) :
    aig.decls.size ≤ (go aig xc curr acc).aig.decls.size := by
  unfold go
  dsimp only
  split
  · refine Nat.le_trans ?_ (by apply go_le_size)
    apply AIG.LawfulVecOperator.le_size (f := AIG.RefVec.ite)
  · simp
termination_by w - curr

theorem blastClz.go_decl_eq (aig : AIG α) (curr : Nat) (acc : AIG.RefVec aig w)
    (xc : AIG.RefVec aig w) :
    ∀ (idx : Nat) h1 h2,
        (go aig xc curr acc).aig.decls[idx]'h1 = aig.decls[idx]'h2 := by
  generalize hgo : go aig xc curr acc = res
  unfold go at hgo
  dsimp only at hgo
  split at hgo
  · rw [← hgo]
    intros
    rw [blastClz.go_decl_eq]
    rw [AIG.LawfulVecOperator.decl_eq (f := AIG.RefVec.ite)]
    apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := AIG.RefVec.ite)
    assumption
  · simp [← hgo]
termination_by w - curr

instance : AIG.LawfulVecOperator α AIG.RefVec blastClz where
  le_size := by
    intros
    unfold blastClz
    dsimp only
    (expose_names; exact blastClz.go_le_size aig 0 (blastConst aig ↑len) input)
  decl_eq := by
    intros
    unfold blastClz
    dsimp only
    (expose_names; exact blastClz.go_decl_eq aig 0 (blastConst aig ↑len) input idx h2 h1)

end bitblast
end BVExpr

end Std.Tactic.BVDecide
