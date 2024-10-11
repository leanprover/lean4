/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
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
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Eq
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Ult
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.GetLsbD

-- TODO

/-!
This module contains the implementation of a bitblaster for general `BitVec` problems with boolean
substructure (`BVLogicalExpr`). It is the main entrypoint into the bitblasting framework.
-/

/-!
This module contains the logic to turn a `BoolExpr Nat` into an `AIG` with maximum subterm sharing,
through the use of a cache that re-uses sub-circuits if possible.
-/

/-!
This module contains the implementation of a bitblaster for `BitVec` expressions (`BVExpr`).
That is, expressions that evaluate to `BitVec` again. Its used as a building block in bitblasting
general `BitVec` problems with boolean substructure.
-/



namespace Std.Tactic.BVDecide

open Std.Sat

mutual

def BVExpr.bitblast.go {w : Nat} (aig : AIG BVBit) (expr : BVExpr w) :
    AIG.ExtendingRefVecEntry aig w :=
  match expr with
  | .var a =>
    let res := BVExpr.bitblast.blastVar aig ⟨a⟩
    ⟨res, AIG.LawfulVecOperator.le_size (f := BVExpr.bitblast.blastVar) ..⟩
  | .const val =>
    let res := BVExpr.bitblast.blastConst aig val
    ⟨res, AIG.LawfulVecOperator.le_size (f := BVExpr.bitblast.blastConst) ..⟩
  | .ofBool logical =>
    let ⟨res, _⟩ := BVLogicalExpr.bitblast.go aig logical
    let aig := res.aig
    let ref := res.ref
    let vec := AIG.RefVec.empty |>.push ref
    ⟨⟨aig, ⟩, sorry⟩
  | .zeroExtend (w := w) v inner =>
    let ⟨⟨aig, evec⟩, haig⟩ := BVExpr.bitblast.go aig inner
    let res := BVExpr.bitblast.blastZeroExtend aig ⟨w, evec⟩
    have := by
      apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := BVExpr.bitblast.blastZeroExtend)
      dsimp only at haig
      assumption
    ⟨res, this⟩
  | .signExtend (w := w) v inner =>
    let ⟨⟨aig, evec⟩, haig⟩ := BVExpr.bitblast.go aig inner
    let res := BVExpr.bitblast.blastSignExtend aig ⟨w, evec⟩
    have := by
      apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := BVExpr.bitblast.blastSignExtend)
      dsimp only at haig
      assumption
    ⟨res, this⟩
  | .bin lhs op rhs =>
    let ⟨⟨aig, lhs⟩, hlaig⟩ := BVExpr.bitblast.go aig lhs
    let ⟨⟨aig, rhs⟩, hraig⟩ := BVExpr.bitblast.go aig rhs
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
      let res := BVExpr.bitblast.blastAdd aig ⟨lhs, rhs⟩
      have := by
        apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := BVExpr.bitblast.blastAdd)
        dsimp only at hlaig hraig
        omega
      ⟨res, this⟩
    | .mul =>
      let res := BVExpr.bitblast.blastMul aig ⟨lhs, rhs⟩
      have := by
        apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := BVExpr.bitblast.blastMul)
        dsimp only at hlaig hraig
        omega
      ⟨res, this⟩
    | .udiv =>
      let res := BVExpr.bitblast.blastUdiv aig ⟨lhs, rhs⟩
      have := by
        apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := BVExpr.bitblast.blastUdiv)
        dsimp only at hlaig hraig
        omega
      ⟨res, this⟩
    | .umod =>
      let res := BVExpr.bitblast.blastUmod aig ⟨lhs, rhs⟩
      have := by
        apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := BVExpr.bitblast.blastUmod)
        dsimp only at hlaig hraig
        omega
      ⟨res, this⟩
  | .un op expr =>
    let ⟨⟨eaig, evec⟩, heaig⟩ := BVExpr.bitblast.go aig expr
    match op with
    | .not =>
        let res := BVExpr.bitblast.blastNot eaig evec
        have := by
          apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := AIG.RefVec.map)
          dsimp only at heaig
          omega
        ⟨res, this⟩
    | .shiftLeftConst distance =>
      let res := BVExpr.bitblast.blastShiftLeftConst eaig ⟨evec, distance⟩
      have := by
        apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := BVExpr.bitblast.blastShiftLeftConst)
        dsimp only at heaig
        assumption
      ⟨res, this⟩
    | .shiftRightConst distance =>
      let res := BVExpr.bitblast.blastShiftRightConst eaig ⟨evec, distance⟩
      have := by
        apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := BVExpr.bitblast.blastShiftRightConst)
        dsimp only at heaig
        assumption
      ⟨res, this⟩
    | .rotateLeft distance =>
      let res := BVExpr.bitblast.blastRotateLeft eaig ⟨evec, distance⟩
      have := by
        apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := BVExpr.bitblast.blastRotateLeft)
        dsimp only at heaig
        assumption
      ⟨res, this⟩
    | .rotateRight distance =>
      let res := BVExpr.bitblast.blastRotateRight eaig ⟨evec, distance⟩
      have := by
        apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := BVExpr.bitblast.blastRotateRight)
        dsimp only at heaig
        assumption
      ⟨res, this⟩
    | .arithShiftRightConst distance =>
      let res := BVExpr.bitblast.blastArithShiftRightConst eaig ⟨evec, distance⟩
      have := by
        apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := BVExpr.bitblast.blastArithShiftRightConst)
        dsimp only at heaig
        assumption
      ⟨res, this⟩
  | .append lhs rhs =>
    let ⟨⟨aig, lhs⟩, hlaig⟩ := BVExpr.bitblast.go aig lhs
    let ⟨⟨aig, rhs⟩, hraig⟩ := BVExpr.bitblast.go aig rhs
    let lhs := lhs.cast <| by
      dsimp only at hlaig hraig
      omega
    let res := BVExpr.bitblast.blastAppend aig ⟨lhs, rhs, by ac_rfl⟩
    have := by
      apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := BVExpr.bitblast.blastAppend)
      dsimp only at hlaig hraig
      omega
    ⟨res, this⟩
  | .replicate n expr =>
    let ⟨⟨aig, expr⟩, haig⟩ := BVExpr.bitblast.go aig expr
    let res := BVExpr.bitblast.blastReplicate aig ⟨n, expr, rfl⟩
    have := by
      apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := BVExpr.bitblast.blastReplicate)
      dsimp only at haig
      assumption
    ⟨res, this⟩
  | .extract start len expr =>
    let ⟨⟨eaig, evec⟩, heaig⟩ := BVExpr.bitblast.go aig expr
    let res := BVExpr.bitblast.blastExtract eaig ⟨evec, start⟩
    have := by
      apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := BVExpr.bitblast.blastExtract)
      dsimp only at heaig
      exact heaig
    ⟨res, this⟩
  | .shiftLeft lhs rhs =>
    let ⟨⟨aig, lhs⟩, hlaig⟩ := BVExpr.bitblast.go aig lhs
    let ⟨⟨aig, rhs⟩, hraig⟩ := BVExpr.bitblast.go aig rhs
    let lhs := lhs.cast <| by
      dsimp only at hlaig hraig
      omega
    let res := BVExpr.bitblast.blastShiftLeft aig ⟨_, lhs, rhs⟩
    have := by
      apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := BVExpr.bitblast.blastShiftLeft)
      dsimp only at hlaig hraig
      omega
    ⟨res, this⟩
  | .shiftRight lhs rhs =>
    let ⟨⟨aig, lhs⟩, hlaig⟩ := BVExpr.bitblast.go aig lhs
    let ⟨⟨aig, rhs⟩, hraig⟩ := BVExpr.bitblast.go aig rhs
    let lhs := lhs.cast <| by
      dsimp only at hlaig hraig
      omega
    let res := BVExpr.bitblast.blastShiftRight aig ⟨_, lhs, rhs⟩
    have := by
      apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := BVExpr.bitblast.blastShiftRight)
      dsimp only at hlaig hraig
      omega
    ⟨res, this⟩

def BVPred.bitblast.go (aig : AIG BVBit) (pred : BVPred) : AIG.ExtendingEntrypoint aig :=
  match pred with
  | .bin lhs op rhs =>
    let ⟨res, _⟩ := BVExpr.bitblast.go aig lhs
    let aig := res.aig
    let lhsRefs := res.vec
    let ⟨res, _⟩ := BVExpr.bitblast.go aig rhs
    let aig := res.aig
    let rhsRefs := res.vec
    let lhsRefs := lhsRefs.cast <| sorry
    match op with
    | .eq => ⟨BVPred.mkEq aig ⟨lhsRefs, rhsRefs⟩, sorry⟩
    | .ult => ⟨BVPred.mkUlt aig ⟨lhsRefs, rhsRefs⟩, sorry⟩
  | .getLsbD expr idx =>
    /-
    Note: This blasts the entire expression up to `w` despite only needing it up to `idx`.
    However the vast majority of operations are interested in all bits so the API is currently
    not designed to support this use case.
    -/
    let ⟨res, _⟩ := BVExpr.bitblast.go aig expr
    let aig := res.aig
    let refs := res.vec
    ⟨BVPred.blastGetLsbD aig ⟨refs, idx⟩, sorry⟩

def BVLogicalExpr.bitblast.go (aig : AIG BVBit) (expr : BVLogicalExpr) : AIG.ExtendingEntrypoint aig :=
  match expr with
  | .literal pred => BVPred.bitblast.go aig pred
  | .const val => ⟨aig.mkConstCached val, (by apply AIG.LawfulOperator.le_size)⟩
  | .not expr =>
    let ⟨⟨aig, exprRef⟩, _⟩ := BVLogicalExpr.bitblast.go aig expr
    let ret := aig.mkNotCached exprRef
    have := AIG.LawfulOperator.le_size (f := AIG.mkNotCached) aig exprRef
    ⟨ret, by dsimp only [ret] at *; omega⟩
  | .gate g lhs rhs =>
    let ⟨⟨aig, lhsRef⟩, lextend⟩ := BVLogicalExpr.bitblast.go aig lhs
    let ⟨⟨aig, rhsRef⟩, rextend⟩ := BVLogicalExpr.bitblast.go aig rhs
    let lhsRef := lhsRef.cast <| by
      dsimp only at rextend ⊢
      omega
    let input := ⟨lhsRef, rhsRef⟩
    match g with
    | .and =>
      let ret := aig.mkAndCached input
      have := AIG.LawfulOperator.le_size (f := AIG.mkAndCached) aig input
      ⟨ret, by dsimp only [ret] at lextend rextend ⊢; omega⟩
    | .xor =>
      let ret := aig.mkXorCached input
      have := AIG.LawfulOperator.le_size (f := AIG.mkXorCached) aig input
      ⟨ret, by dsimp only [ret] at lextend rextend ⊢; omega⟩
    | .beq =>
      let ret := aig.mkBEqCached input
      have := AIG.LawfulOperator.le_size (f := AIG.mkBEqCached) aig input
      ⟨ret, by dsimp only [ret] at lextend rextend ⊢; omega⟩

end


namespace BVExpr

def bitblast (aig : AIG BVBit) (expr : BVExpr w) : AIG.RefVecEntry BVBit w :=
  bitblast.go aig expr |>.val

theorem bitblast.go_decl_eq (aig : AIG BVBit) (expr : BVExpr w) :
    ∀ (idx : Nat) (h1) (h2), (go aig expr).val.aig.decls[idx]'h2 = aig.decls[idx]'h1 := by
  intros idx h1 h2
  sorry
/-
  induction expr generalizing aig with
  | var =>
    dsimp only [go]
    rw [AIG.LawfulVecOperator.decl_eq (f := blastVar)]
  | const =>
    dsimp only [go]
    rw [AIG.LawfulVecOperator.decl_eq (f := blastConst)]
  | ofBool => sorry
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
  -/

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

namespace BVPred

def bitblast (aig : AIG BVBit) (pred : BVPred) : AIG.Entrypoint BVBit :=
  bitblast.go aig pred |>.val

instance : AIG.LawfulOperator BVBit (fun _ => BVPred) bitblast where
  le_size := by sorry
    /-
    intro aig pred
    unfold bitblast
    cases pred with
    | bin lhs op rhs =>
      cases op with
      | eq =>
        apply AIG.LawfulOperator.le_size_of_le_aig_size (f := mkEq)
        apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := BVExpr.bitblast)
        apply AIG.LawfulVecOperator.le_size (f := BVExpr.bitblast)
      | ult =>
        apply AIG.LawfulOperator.le_size_of_le_aig_size (f := mkUlt)
        apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := BVExpr.bitblast)
        apply AIG.LawfulVecOperator.le_size (f := BVExpr.bitblast)
    | getLsbD expr idx =>
      apply AIG.LawfulOperator.le_size_of_le_aig_size (f := blastGetLsbD)
      apply AIG.LawfulVecOperator.le_size (f := BVExpr.bitblast)
    -/
  decl_eq := by sorry
    /-
    intro aig pred idx h1 h2
    cases pred with
    | bin lhs op rhs =>
      cases op with
      | eq =>
        simp only [bitblast]
        rw [AIG.LawfulOperator.decl_eq (f := mkEq)]
        rw [AIG.LawfulVecOperator.decl_eq (f := BVExpr.bitblast)]
        rw [AIG.LawfulVecOperator.decl_eq (f := BVExpr.bitblast)]
        · apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := BVExpr.bitblast)
          assumption
        · apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := BVExpr.bitblast)
          apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := BVExpr.bitblast)
          assumption
      | ult =>
        simp only [bitblast]
        rw [AIG.LawfulOperator.decl_eq (f := mkUlt)]
        rw [AIG.LawfulVecOperator.decl_eq (f := BVExpr.bitblast)]
        rw [AIG.LawfulVecOperator.decl_eq (f := BVExpr.bitblast)]
        · apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := BVExpr.bitblast)
          assumption
        · apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := BVExpr.bitblast)
          apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := BVExpr.bitblast)
          assumption
    | getLsbD expr idx =>
      simp only [bitblast]
      rw [AIG.LawfulOperator.decl_eq (f := blastGetLsbD)]
      rw [AIG.LawfulVecOperator.decl_eq (f := BVExpr.bitblast)]
      apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := BVExpr.bitblast)
      assumption
    -/

end BVPred


namespace BVLogicalExpr

def bitblast (expr : BVLogicalExpr) : AIG.Entrypoint BVBit :=
  bitblast.go AIG.empty expr |>.val

namespace bitblast

theorem go_decls_size_le (expr : BVLogicalExpr) (aig : AIG BVBit) :
    aig.decls.size ≤ (bitblast.go aig expr).val.aig.decls.size :=
  (bitblast.go aig expr).property

theorem go_decl_eq (idx) (aig : AIG BVBit) (h : idx < aig.decls.size) (hbounds) :
    (bitblast.go aig expr).val.aig.decls[idx]'hbounds = aig.decls[idx] := by
  sorry
  /-
  induction expr generalizing aig with
  | const =>
    simp only [go]
    rw [AIG.LawfulOperator.decl_eq (f := mkConstCached)]
  | literal =>
    simp only [go]
    rw [AIG.LawfulOperator.decl_eq (f := BVPred.bitblast)]
  | not expr ih =>
    simp only [go]
    have := go_decls_size_le expr aig
    specialize ih aig (by omega) (by omega)
    rw [AIG.LawfulOperator.decl_eq (f := mkNotCached)]
    assumption
  | gate g lhs rhs lih rih =>
    have := go_decls_size_le lhs aig
    have := go_decls_size_le rhs (go aig lhs).val.aig
    specialize lih aig (by omega) (by omega)
    specialize rih (go aig lhs).val.aig (by omega) (by omega)
    cases g with
    | and =>
      simp only [go]
      rw [AIG.LawfulOperator.decl_eq (f := mkAndCached), rih, lih]
    | xor =>
      simp only [go]
      rw [AIG.LawfulOperator.decl_eq (f := mkXorCached), rih, lih]
    | beq =>
      simp only [go]
      rw [AIG.LawfulOperator.decl_eq (f := mkBEqCached), rih, lih]
    -/

theorem go_isPrefix_aig {aig : AIG BVBit} : AIG.IsPrefix aig.decls (go aig expr).val.aig.decls := by
  apply AIG.IsPrefix.of
  · intro idx h
    apply go_decl_eq
  · apply go_decls_size_le

open AIG in
@[simp]
theorem go_denote_entry (entry : Entrypoint BVBit) {h} :
    ⟦(go entry.aig expr).val.aig, ⟨entry.ref.gate, h⟩, assign⟧ = ⟦entry, assign⟧ := by
  apply denote.eq_of_isPrefix
  apply go_isPrefix_aig

end bitblast

end BVLogicalExpr

end Std.Tactic.BVDecide
