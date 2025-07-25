/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luisa Cicolini, Siddharth Bhat, Henrik Böving
-/

module

prelude
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Const
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Sub
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Eq
public import Std.Sat.AIG.If

@[expose] public section

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
  let zero : AIG.RefVec aig w := blastConst aig (w := w) 0
  go aig x 0 zero
where
  go (aig : AIG α) (x : AIG.RefVec aig w) (n : Nat) (acc : AIG.RefVec aig w) :=
    if hc : n < w then
      let one : AIG.RefVec aig w := blastConst aig (w := w) 1
      let res : AIG.RefVecEntry α w := blastAdd aig ⟨acc, one⟩
      let aig := res.aig
      let add := res.vec
      have := AIG.LawfulVecOperator.le_size (f := blastAdd) ..
      let acc := acc.cast this
      let x := x.cast this
      let res := AIG.RefVec.ite aig ⟨x.get n (by omega), add, acc⟩
      let aig := res.aig
      let acc := res.vec
      have := AIG.LawfulVecOperator.le_size (f := AIG.RefVec.ite) ..
      let add := add.cast this
      let x := x.cast this
      go aig x (n + 1) acc
    else
      ⟨aig, acc⟩
  termination_by (w - n)

namespace blastPopCount

end blastPopCount

theorem blastPopCount.go_le_size (aig : AIG α) (curr : Nat)(acc : AIG.RefVec aig w)
    (xc : AIG.RefVec aig w) :
    aig.decls.size ≤ (go aig xc curr acc).aig.decls.size := by
  unfold go
  dsimp only
  split
  · refine Nat.le_trans ?_ (by apply go_le_size)
    apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := AIG.RefVec.ite)
    apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := blastAdd)
    simp
  · simp

theorem blastPopCount.go_decl_eq (aig : AIG α) (curr : Nat)  (acc : AIG.RefVec aig w)
    (xc : AIG.RefVec aig w) :
    ∀ (idx : Nat) h1 h2,
        (go aig xc curr acc).aig.decls[idx]'h1 = aig.decls[idx]'h2 := by
  generalize hgo : go aig xc curr acc = res
  unfold go at hgo
  dsimp only at hgo
  split at hgo
  · rw [← hgo]
    intros
    rename_i h
    rw [blastPopCount.go_decl_eq, AIG.LawfulVecOperator.decl_eq (f := AIG.RefVec.ite),
      AIG.LawfulVecOperator.decl_eq (f := blastAdd)]
    apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastAdd)
    · exact h
    · intros
      apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := AIG.RefVec.ite)
      apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastAdd)
      exact h
  · simp [← hgo]

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
