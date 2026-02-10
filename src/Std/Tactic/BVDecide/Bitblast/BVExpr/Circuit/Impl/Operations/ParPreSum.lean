/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luisa Cicolini
-/
module

prelude
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Const
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Sub
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Extract
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Append
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.ZeroExtend
public import Std.Sat.AIG.If

import Init.Omega

@[expose] public section

/-!
This module contains the implementation of a bitblaster for `BitVec.hAdd`.
-/

namespace Std.Tactic.BVDecide

open Std.Sat

variable [Hashable α] [DecidableEq α]

namespace BVExpr
namespace bitblast

structure ParPreSumTarget (aig : AIG α) (len : Nat) where
  {w : Nat}
  len : Nat
  inner : AIG.RefVec aig w

/-- Given a vector of references belonging to the same AIG `oldParSum`,
  we create a node to add the `curr`-th couple of elements and push the add node to `newParSum` -/
def blastParPreSumLayer (aig : AIG α)
  (iter_num : Nat)
  (old_layer : AIG.RefVec aig (old_length * w))
  (new_layer : AIG.RefVec aig (iter_num * w))
  (hold : 2 * (iter_num - 1) < old_length) :
   AIG.RefVecEntry α ((old_length + 1)/2 * w) :=
  if  hlen : 0 < old_length - (iter_num * 2) then
    -- lhs
    let targetExtract : ExtractTarget aig w := {vec := old_layer, start := 2 * iter_num * w}
    let res := blastExtract aig targetExtract
    let aig := res.aig
    let op1 : aig.RefVec w := res.vec
    have := AIG.LawfulVecOperator.le_size (f := blastExtract) ..
    let old_layer := old_layer.cast (aig2 := aig) this
    let new_layer := new_layer.cast (aig2 := aig) this
    -- rhs
    let targetExtract : ExtractTarget aig w := {vec := old_layer, start := (2 * iter_num + 1) * w}
    let res := blastExtract aig targetExtract
    let aig := res.aig
    let op2 : aig.RefVec w := res.vec
    have := AIG.LawfulVecOperator.le_size (f := blastExtract) (input := targetExtract)
    let old_layer := old_layer.cast this
    let new_layer := new_layer.cast this
    let op1 := op1.cast (aig2 := aig) this
    -- add
    let res := blastAdd aig ⟨op1, op2⟩
    let aig := res.aig
    let add := res.vec
    have := AIG.LawfulVecOperator.le_size (f := blastAdd) ..
    let old_layer := old_layer.cast this
    let new_layer := new_layer.cast this
    let op1 := op1.cast this
    let op2 := op2.cast this
    have hcast : w + iter_num * w = (iter_num + 1) * w:= by simp [Nat.add_mul]; omega
    let targetAppend : AppendTarget aig ((iter_num + 1) * w ) :=
        {lhs := add, rhs := new_layer, h := by omega}
    let res := blastAppend (aig := aig) (target:= targetAppend)
    let aig := res.aig
    let new_layer' := res.vec
    have := AIG.LawfulVecOperator.le_size (f := blastAppend) ..
    let old_layer := old_layer.cast this
    blastParPreSumLayer aig (iter_num + 1) old_layer new_layer' (by omega)
  else
    have h : iter_num = (old_length + 1) / 2 := by omega
    ⟨aig, h ▸ new_layer⟩
termination_by old_length - iter_num * 2

theorem blastParPreSumLayer_le_size (aig : AIG α) (iter_num: Nat)
      (old_layer : AIG.RefVec aig (old_length * w)) (new_layer : AIG.RefVec aig (iter_num * w))
      (hold : 2 * (iter_num - 1) < old_length) :
    aig.decls.size ≤ (blastParPreSumLayer aig iter_num old_layer new_layer hold).aig.decls.size := by
  unfold blastParPreSumLayer
  dsimp only
  split
  · simp
    <;> (refine Nat.le_trans ?_ (by apply blastParPreSumLayer_le_size); apply AIG.LawfulVecOperator.le_size)
  · simp

theorem blastParPreSumLayer_decl_eq (aig : AIG α) (iter_num: Nat)
      (old_layer : AIG.RefVec aig (old_length * w)) (new_layer : AIG.RefVec aig (iter_num * w))
      (hold : 2 * (iter_num - 1) < old_length) :
    ∀ (idx : Nat) h1 h2,
      (blastParPreSumLayer aig iter_num old_layer new_layer hold).aig.decls[idx]'h1 = aig.decls[idx]'h2 := by
  generalize hres : blastParPreSumLayer aig iter_num old_layer new_layer hold= res
  unfold blastParPreSumLayer at hres
  dsimp only at hres
  split at hres
  · simp at hres
    · rw [← hres]
      intros
      rw [blastParPreSumLayer_decl_eq]
      · apply AIG.LawfulVecOperator.decl_eq (f := blastAdd)
      · apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastAdd)
        assumption
  · simp [← hres]

def blastParPreSumTree
  (aig : AIG α) (l : AIG.RefVec aig (l_length * w)) (h : 0 < l_length) : AIG.RefVecEntry α w :=
  if hlt : 1 < l_length  then
    have hcastZero : 0 = 0 / 2 * w := by omega
    let initAcc := blastConst (aig := aig) (w := 0) (val := 0)
    let res := blastParPreSumLayer aig 0 l (hcastZero▸initAcc) (by omega)
    let aig := res.aig
    let new_layer := res.vec
    blastParPreSumTree (aig := aig) (l := new_layer) (by omega)
  else
    have hcast : l_length * w = w := by simp [show l_length = 1 by omega]
    ⟨aig, hcast▸l⟩
termination_by l_length

theorem blastParPreSumTree_le_size (aig : AIG α)
      (old_layer : AIG.RefVec aig (old_length * w)) (h : 0 < old_length) :
    aig.decls.size ≤ (blastParPreSumTree aig old_layer h).aig.decls.size := by
  unfold blastParPreSumTree
  dsimp only
  split
  · simp only [BitVec.ofNat_eq_ofNat, Nat.reduceDiv]
    apply Nat.le_trans _ (by apply blastParPreSumTree_le_size)
    apply blastParPreSumLayer_le_size
  · simp

theorem blastParPreSumTree_decl_eq (aig : AIG α)
      (old_layer : AIG.RefVec aig (old_length * w)) (h : 0 < old_length) :
    ∀ (idx : Nat) h1 h2,
      (blastParPreSumTree aig old_layer h).aig.decls[idx]'h1 = aig.decls[idx]'h2 := by
  generalize hres : blastParPreSumTree aig old_layer h = res
  unfold blastParPreSumTree at hres
  dsimp only at hres
  split at hres
  · simp at hres
    · rw [← hres]
      intros i h1 h2
      rw [blastParPreSumTree_decl_eq]
      · apply blastParPreSumLayer_decl_eq
      · apply Nat.lt_of_lt_of_le h2
        apply blastParPreSumLayer_le_size
  · simp [← hres]

/-- We first extend all the single bits in the input BitVec w to have width `w`, then compute
the parallel prefix sum given these bits.-/
def blastParPreSum (aig : AIG α) (x : ParPreSumTarget aig l) :
    AIG.RefVecEntry α l :=
  if  hw0 : l = 0 then
    let res := blastConst aig (w := l) (val := 0)
    ⟨aig, res⟩
  else
    let w := x.w
    if hle : w ≤ l then
      /- zero-extend to `l` -/
      let zextTarget : AIG.ExtendTarget aig l := {w := w, vec := x.inner}
      let res := blastZeroExtend aig zextTarget
      ⟨res.aig, res.vec⟩
    else if hmodlt : 0 < w % l then
      /- zero-extend to the closest multiple of `l` -/
      have hzero : (w - w % l) % l = 0 := by
        apply Nat.sub_mod_eq_zero_of_mod_eq
        rw [Nat.mod_mod]
      let diff := (l - (w % l))
      have hmodlt' := Nat.mod_lt (y := l) (x := w) (by omega)
      have hmodeq : (w + diff) % l = 0 := by
        simp only [diff]
        rw [← Nat.add_sub_assoc (by omega), Nat.add_comm,
          show l + w - w % l = l + (w - w % l) by omega]
        simp [hzero]
      let zextTarget : AIG.ExtendTarget aig (w + diff) := {w := w, vec := x.inner}
      let res := blastZeroExtend aig zextTarget
      let aig := res.aig
      let vec := res.vec
      let init_length := (w + diff) / l
      have hcast : w + diff = init_length * l := by
        simp only [init_length]
        apply Eq.symm
        apply (Nat.dvd_iff_div_mul_eq (w + diff) l ).mp
        apply (Nat.mod_eq_sub_iff ?_ ?_).mp
        <;> omega
      let castVec : AIG.RefVec aig (init_length * l) :=
                      {refs := vec.refs.cast hcast,
                        hrefs := by simp [aig, vec.hrefs]}
      blastParPreSumTree aig (l_length := init_length) (by simp [init_length]; omega) (l := castVec)
    else
      /- cast and build parPreSum directly -/
      let init_length := w / l
      have hcast : x.w = init_length * l := by
        simp only [init_length]
        apply Eq.symm
        apply (Nat.dvd_iff_div_mul_eq w l ).mp
        refine Int.ofNat_dvd.mp ?_
        omega
      let castVec : AIG.RefVec aig (init_length * l) :=
                      {refs := x.inner.refs.cast hcast,
                        hrefs := by simp [x.inner.hrefs]}
      blastParPreSumTree aig (l_length := init_length) (by simp [init_length]; omega) (l := castVec)


theorem blastParPreSum_le_size (aig : AIG α) (l : Nat) (x : ParPreSumTarget aig l) :
    aig.decls.size ≤ (blastParPreSum aig x).aig.decls.size := by
  unfold blastParPreSum
  split
  · simp
  · simp
    split
    · apply AIG.LawfulVecOperator.le_size
    · split
      · let w := x.w
        let diff := l - w % l;
        let zextTarget : AIG.ExtendTarget aig (w + diff) := { w := w, vec := x.inner };
        have htmp : aig.decls.size ≤ (blastZeroExtend aig zextTarget).aig.decls.size := by
          exact AIG.LawfulVecOperator.le_size aig zextTarget
        apply Nat.le_trans htmp
        apply blastParPreSumTree_le_size
      · apply blastParPreSumTree_le_size

theorem blastParPreSum_decl_eq (aig : AIG α)
      (x : ParPreSumTarget aig l) :
    ∀ (idx : Nat) h1 h2,
      (blastParPreSum aig x).aig.decls[idx]'h1 = aig.decls[idx]'h2 := by
  generalize hgo : blastParPreSum aig x = res
  unfold blastParPreSum at hgo
  dsimp only at hgo
  split at hgo
  · rw [← hgo]
    simp
  · split at hgo
    · simp only [← hgo]
      intros i h1 h2
      apply AIG.LawfulVecOperator.decl_eq
    · split at hgo
      · rw [← hgo]
        intros i h1 h2
        rw [blastParPreSumTree_decl_eq]
        · apply AIG.LawfulVecOperator.decl_eq
        · apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size
          exact h2
      · rw [← hgo]
        apply blastParPreSumTree_decl_eq

instance : AIG.LawfulVecOperator α ParPreSumTarget blastParPreSum where
  le_size := by
    intros
    apply blastParPreSum_le_size
  decl_eq := by
    intros
    apply blastParPreSum_decl_eq


end bitblast
end BVExpr

end Std.Tactic.BVDecide
