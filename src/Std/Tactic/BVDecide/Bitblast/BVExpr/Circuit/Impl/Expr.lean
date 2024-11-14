/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Init.Data.AC
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Var
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Const
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Not
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.ShiftLeft
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.ShiftRight
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Add
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.ZeroExtend
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Append
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Replicate
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Extract
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.RotateLeft
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.RotateRight
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.SignExtend
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Mul
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Udiv
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Umod

/-!
This module contains the implementation of a bitblaster for `BitVec` expressions (`BVExpr`).
That is, expressions that evaluate to `BitVec` again. Its used as a building block in bitblasting
general `BitVec` problems with boolean substructure.
-/

namespace Std.Tactic.BVDecide

open Std.Sat

namespace BVExpr

def bitblast (aig : AIG BVBit) (expr : BVExpr w) : AIG.RefVecEntry BVBit w :=
  go aig expr |>.val
where
  go {w : Nat} (aig : AIG BVBit) (expr : BVExpr w) : AIG.ExtendingRefVecEntry aig w :=
    match expr with
    | .var a =>
      let res := bitblast.blastVar aig ⟨a⟩
      ⟨res, AIG.LawfulVecOperator.le_size (f := bitblast.blastVar) ..⟩
    | .const val =>
      let res := bitblast.blastConst aig val
      ⟨res, AIG.LawfulVecOperator.le_size (f := bitblast.blastConst) ..⟩
    | .zeroExtend (w := w) v inner =>
      let ⟨⟨aig, evec⟩, haig⟩ := go aig inner
      let res := bitblast.blastZeroExtend aig ⟨w, evec⟩
      have := by
        apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := bitblast.blastZeroExtend)
        dsimp only at haig
        assumption
      ⟨res, this⟩
    | .signExtend (w := w) v inner =>
      let ⟨⟨aig, evec⟩, haig⟩ := go aig inner
      let res := bitblast.blastSignExtend aig ⟨w, evec⟩
      have := by
        apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := bitblast.blastSignExtend)
        dsimp only at haig
        assumption
      ⟨res, this⟩
    | .bin lhs op rhs =>
      let ⟨⟨aig, lhs⟩, hlaig⟩ := go aig lhs
      let ⟨⟨aig, rhs⟩, hraig⟩ := go aig rhs
      let lhs := lhs.cast <| by
        dsimp only at hlaig hraig
        omega
      match op with
      | .and =>
         let res := AIG.RefVec.zip aig ⟨⟨lhs, rhs⟩, AIG.mkAndCached⟩
         have := by
           apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := AIG.RefVec.zip)
           dsimp only at hlaig hraig
           omega
         ⟨res, this⟩
      | .or =>
         let res := AIG.RefVec.zip aig ⟨⟨lhs, rhs⟩, AIG.mkOrCached⟩
         have := by
           apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := AIG.RefVec.zip)
           dsimp only at hlaig hraig
           omega
         ⟨res, this⟩
      | .xor =>
         let res := AIG.RefVec.zip aig ⟨⟨lhs, rhs⟩, AIG.mkXorCached⟩
         have := by
           apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := AIG.RefVec.zip)
           dsimp only at hlaig hraig
           omega
         ⟨res, this⟩
      | .add =>
        let res := bitblast.blastAdd aig ⟨lhs, rhs⟩
        have := by
          apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := bitblast.blastAdd)
          dsimp only at hlaig hraig
          omega
        ⟨res, this⟩
      | .mul =>
        let res := bitblast.blastMul aig ⟨lhs, rhs⟩
        have := by
          apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := bitblast.blastMul)
          dsimp only at hlaig hraig
          omega
        ⟨res, this⟩
      | .udiv =>
        let res := bitblast.blastUdiv aig ⟨lhs, rhs⟩
        have := by
          apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := bitblast.blastUdiv)
          dsimp only at hlaig hraig
          omega
        ⟨res, this⟩
      | .umod =>
        let res := bitblast.blastUmod aig ⟨lhs, rhs⟩
        have := by
          apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := bitblast.blastUmod)
          dsimp only at hlaig hraig
          omega
        ⟨res, this⟩
    | .un op expr =>
      let ⟨⟨eaig, evec⟩, heaig⟩ := go aig expr
      match op with
      | .not =>
          let res := bitblast.blastNot eaig evec
          have := by
            apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := AIG.RefVec.map)
            dsimp only at heaig
            omega
          ⟨res, this⟩
      | .shiftLeftConst distance =>
        let res := bitblast.blastShiftLeftConst eaig ⟨evec, distance⟩
        have := by
          apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := bitblast.blastShiftLeftConst)
          dsimp only at heaig
          assumption
        ⟨res, this⟩
      | .shiftRightConst distance =>
        let res := bitblast.blastShiftRightConst eaig ⟨evec, distance⟩
        have := by
          apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := bitblast.blastShiftRightConst)
          dsimp only at heaig
          assumption
        ⟨res, this⟩
      | .rotateLeft distance =>
        let res := bitblast.blastRotateLeft eaig ⟨evec, distance⟩
        have := by
          apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := bitblast.blastRotateLeft)
          dsimp only at heaig
          assumption
        ⟨res, this⟩
      | .rotateRight distance =>
        let res := bitblast.blastRotateRight eaig ⟨evec, distance⟩
        have := by
          apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := bitblast.blastRotateRight)
          dsimp only at heaig
          assumption
        ⟨res, this⟩
      | .arithShiftRightConst distance =>
        let res := bitblast.blastArithShiftRightConst eaig ⟨evec, distance⟩
        have := by
          apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := bitblast.blastArithShiftRightConst)
          dsimp only at heaig
          assumption
        ⟨res, this⟩
    | .append lhs rhs =>
      let ⟨⟨aig, lhs⟩, hlaig⟩ := go aig lhs
      let ⟨⟨aig, rhs⟩, hraig⟩ := go aig rhs
      let lhs := lhs.cast <| by
        dsimp only at hlaig hraig
        omega
      let res := bitblast.blastAppend aig ⟨lhs, rhs, by ac_rfl⟩
      have := by
        apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := bitblast.blastAppend)
        dsimp only at hlaig hraig
        omega
      ⟨res, this⟩
    | .replicate n expr =>
      let ⟨⟨aig, expr⟩, haig⟩ := go aig expr
      let res := bitblast.blastReplicate aig ⟨n, expr, rfl⟩
      have := by
        apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := bitblast.blastReplicate)
        dsimp only at haig
        assumption
      ⟨res, this⟩
    | .extract start len expr =>
      let ⟨⟨eaig, evec⟩, heaig⟩ := go aig expr
      let res := bitblast.blastExtract eaig ⟨evec, start⟩
      have := by
        apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := bitblast.blastExtract)
        dsimp only at heaig
        exact heaig
      ⟨res, this⟩
    | .shiftLeft lhs rhs =>
      let ⟨⟨aig, lhs⟩, hlaig⟩ := go aig lhs
      let ⟨⟨aig, rhs⟩, hraig⟩ := go aig rhs
      let lhs := lhs.cast <| by
        dsimp only at hlaig hraig
        omega
      let res := bitblast.blastShiftLeft aig ⟨_, lhs, rhs⟩
      have := by
        apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := bitblast.blastShiftLeft)
        dsimp only at hlaig hraig
        omega
      ⟨res, this⟩
    | .shiftRight lhs rhs =>
      let ⟨⟨aig, lhs⟩, hlaig⟩ := go aig lhs
      let ⟨⟨aig, rhs⟩, hraig⟩ := go aig rhs
      let lhs := lhs.cast <| by
        dsimp only at hlaig hraig
        omega
      let res := bitblast.blastShiftRight aig ⟨_, lhs, rhs⟩
      have := by
        apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := bitblast.blastShiftRight)
        dsimp only at hlaig hraig
        omega
      ⟨res, this⟩
    | .arithShiftRight lhs rhs =>
      let ⟨⟨aig, lhs⟩, hlaig⟩ := go aig lhs
      let ⟨⟨aig, rhs⟩, hraig⟩ := go aig rhs
      let lhs := lhs.cast <| by
        dsimp only at hlaig hraig
        omega
      let res := bitblast.blastArithShiftRight aig ⟨_, lhs, rhs⟩
      have := by
        apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := bitblast.blastArithShiftRight)
        dsimp only at hlaig hraig
        omega
      ⟨res, this⟩

theorem bitblast.go_decl_eq (aig : AIG BVBit) (expr : BVExpr w) :
    ∀ (idx : Nat) (h1) (h2), (go aig expr).val.aig.decls[idx]'h2 = aig.decls[idx]'h1 := by
  intros idx h1 h2
  induction expr generalizing aig with
  | var =>
    dsimp only [go]
    rw [AIG.LawfulVecOperator.decl_eq (f := blastVar)]
  | const =>
    dsimp only [go]
    rw [AIG.LawfulVecOperator.decl_eq (f := blastConst)]
  | bin lhs op rhs lih rih =>
    match op with
    | .and | .or | .xor | .add | .mul | .udiv | .umod =>
      dsimp only [go]
      have := (bitblast.go aig lhs).property
      have := (go (go aig lhs).1.aig rhs).property
      have := (bitblast.go aig lhs).property
      rw [AIG.LawfulVecOperator.decl_eq]
      rw [rih, lih]
      · omega
      · apply Nat.lt_of_lt_of_le h1 -- omega cannot do this :(
        apply Nat.le_trans <;> assumption
  | un op expr ih =>
    match op with
    | .not | .shiftLeftConst .. | .shiftRightConst .. | .rotateLeft .. | .rotateRight ..
    | .arithShiftRightConst .. =>
      dsimp only [go]
      rw [AIG.LawfulVecOperator.decl_eq]
      rw [ih]
      have := (go aig expr).property
      omega
  | zeroExtend w inner ih =>
    dsimp only [go]
    rw [AIG.LawfulVecOperator.decl_eq (f := blastZeroExtend)]
    rw [ih]
    have := (go aig inner).property
    omega
  | signExtend w inner ih =>
    dsimp only [go]
    rw [AIG.LawfulVecOperator.decl_eq (f := blastSignExtend)]
    rw [ih]
    have := (go aig inner).property
    omega
  | append lhs rhs lih rih =>
    dsimp only [go]
    have := (bitblast.go aig lhs).property
    have := (bitblast.go aig lhs).property
    have := (go (go aig lhs).1.aig rhs).property
    rw [AIG.LawfulVecOperator.decl_eq (f := blastAppend)]
    rw [rih, lih]
    · omega
    · apply Nat.lt_of_lt_of_le h1
      apply Nat.le_trans <;> assumption
  | replicate n inner ih =>
    dsimp only [go]
    rw [AIG.LawfulVecOperator.decl_eq (f := blastReplicate)]
    rw [ih]
    have := (go aig inner).property
    omega
  | extract hi lo inner ih =>
    dsimp only [go]
    rw [AIG.LawfulVecOperator.decl_eq (f := blastExtract)]
    rw [ih]
    have := (go aig inner).property
    omega
  | shiftLeft lhs rhs lih rih =>
    dsimp only [go]
    have := (bitblast.go aig lhs).property
    have := (bitblast.go aig lhs).property
    have := (go (go aig lhs).1.aig rhs).property
    rw [AIG.LawfulVecOperator.decl_eq (f := blastShiftLeft)]
    rw [rih, lih]
    · omega
    · apply Nat.lt_of_lt_of_le h1
      apply Nat.le_trans <;> assumption
  | shiftRight lhs rhs lih rih =>
    dsimp only [go]
    have := (bitblast.go aig lhs).property
    have := (bitblast.go aig lhs).property
    have := (go (go aig lhs).1.aig rhs).property
    rw [AIG.LawfulVecOperator.decl_eq (f := blastShiftRight)]
    rw [rih, lih]
    · omega
    · apply Nat.lt_of_lt_of_le h1
      apply Nat.le_trans <;> assumption
  | arithShiftRight lhs rhs lih rih =>
    dsimp only [go]
    have := (bitblast.go aig lhs).property
    have := (bitblast.go aig lhs).property
    have := (go (go aig lhs).1.aig rhs).property
    rw [AIG.LawfulVecOperator.decl_eq (f := blastArithShiftRight)]
    rw [rih, lih]
    · omega
    · apply Nat.lt_of_lt_of_le h1
      apply Nat.le_trans <;> assumption

instance : AIG.LawfulVecOperator BVBit (fun _ w => BVExpr w) bitblast where
  le_size := by
    intro _ aig expr
    unfold bitblast
    exact (bitblast.go aig expr).property
  decl_eq := by
    intros
    unfold bitblast
    apply bitblast.go_decl_eq

end BVExpr

end Std.Tactic.BVDecide
