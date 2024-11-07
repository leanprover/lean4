/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Lean.Elab.Tactic.BVDecide.Frontend.BVDecide.ReifiedBVLogical
import Lean.Elab.Tactic.BVDecide.Frontend.BVDecide.ReifiedLemmas

/-!
Reifies `BitVec` problems with boolean substructure.
-/

namespace Lean.Elab.Tactic.BVDecide
namespace Frontend

open Std.Tactic.BVDecide
open Lean.Meta

mutual

/--
Reify an `Expr` that's a constant-width `BitVec`.
Unless this function is called on something that is not a constant-width `BitVec` it is always
going to return `some`.
-/
partial def ReifiedBVExpr.of (x : Expr) : LemmaM (Option ReifiedBVExpr) := do
  goOrAtom x
where
  /--
  Reify `x`, returns `none` if the reification procedure failed.
  -/
  go (x : Expr) : LemmaM (Option ReifiedBVExpr) := do
    match_expr x with
    | BitVec.ofNat _ _ => goBvLit x
    | HAnd.hAnd _ _ _ _ lhsExpr rhsExpr =>
      binaryReflection lhsExpr rhsExpr .and ``Std.Tactic.BVDecide.Reflect.BitVec.and_congr
    | HOr.hOr _ _ _ _ lhsExpr rhsExpr =>
      binaryReflection lhsExpr rhsExpr .or ``Std.Tactic.BVDecide.Reflect.BitVec.or_congr
    | HXor.hXor _ _ _ _ lhsExpr rhsExpr =>
      binaryReflection lhsExpr rhsExpr .xor ``Std.Tactic.BVDecide.Reflect.BitVec.xor_congr
    | HAdd.hAdd _ _ _ _ lhsExpr rhsExpr =>
      binaryReflection lhsExpr rhsExpr .add ``Std.Tactic.BVDecide.Reflect.BitVec.add_congr
    | HMul.hMul _ _ _ _ lhsExpr rhsExpr =>
      binaryReflection lhsExpr rhsExpr .mul ``Std.Tactic.BVDecide.Reflect.BitVec.mul_congr
    | HDiv.hDiv _ _ _ _ lhsExpr rhsExpr =>
      binaryReflection lhsExpr rhsExpr .udiv ``Std.Tactic.BVDecide.Reflect.BitVec.udiv_congr
    | HMod.hMod _ _ _ _ lhsExpr rhsExpr =>
      binaryReflection lhsExpr rhsExpr .umod ``Std.Tactic.BVDecide.Reflect.BitVec.umod_congr
    | Complement.complement _ _ innerExpr =>
      unaryReflection innerExpr .not ``Std.Tactic.BVDecide.Reflect.BitVec.not_congr
    | HShiftLeft.hShiftLeft _ β _ _ innerExpr distanceExpr =>
      let distance? ← ReifiedBVExpr.getNatOrBvValue? β distanceExpr
      if distance?.isSome then
        shiftConstReflection
          β
          distanceExpr
          innerExpr
          .shiftLeftConst
          ``BVUnOp.shiftLeftConst
          ``Std.Tactic.BVDecide.Reflect.BitVec.shiftLeftNat_congr
      else
        let_expr BitVec _ := β | return none
        shiftReflection
          distanceExpr
          innerExpr
          .shiftLeft
          ``BVExpr.shiftLeft
          ``Std.Tactic.BVDecide.Reflect.BitVec.shiftLeft_congr
    | HShiftRight.hShiftRight _ β _ _ innerExpr distanceExpr =>
      let distance? ← ReifiedBVExpr.getNatOrBvValue? β distanceExpr
      if distance?.isSome then
        shiftConstReflection
          β
          distanceExpr
          innerExpr
          .shiftRightConst
          ``BVUnOp.shiftRightConst
          ``Std.Tactic.BVDecide.Reflect.BitVec.shiftRightNat_congr
      else
        let_expr BitVec _ := β | return none
        shiftReflection
          distanceExpr
          innerExpr
          .shiftRight
          ``BVExpr.shiftRight
          ``Std.Tactic.BVDecide.Reflect.BitVec.shiftRight_congr
    | BitVec.sshiftRight _ innerExpr distanceExpr =>
      let some distance ← getNatValue? distanceExpr | return none
      shiftConstLikeReflection
        distance
        innerExpr
        .arithShiftRightConst
        ``BVUnOp.arithShiftRightConst
        ``Std.Tactic.BVDecide.Reflect.BitVec.arithShiftRightNat_congr
    | BitVec.sshiftRight' _ _ innerExpr distanceExpr =>
      shiftReflection
        distanceExpr
        innerExpr
        .arithShiftRight
        ``BVExpr.arithShiftRight
        ``Std.Tactic.BVDecide.Reflect.BitVec.arithShiftRight_congr
    | BitVec.zeroExtend _ newWidthExpr innerExpr =>
      let some newWidth ← getNatValue? newWidthExpr | return none
      let some inner ← goOrAtom innerExpr | return none
      let bvExpr := .zeroExtend newWidth inner.bvExpr
      let expr :=
        mkApp3
          (mkConst ``BVExpr.zeroExtend)
          (toExpr inner.width)
          newWidthExpr
          inner.expr
      let proof := do
        let innerEval ← ReifiedBVExpr.mkEvalExpr inner.width inner.expr
        let innerProof ← inner.evalsAtAtoms
        return mkApp5 (mkConst ``Std.Tactic.BVDecide.Reflect.BitVec.zeroExtend_congr)
          newWidthExpr
          (toExpr inner.width)
          innerExpr
          innerEval
          innerProof
      return some ⟨newWidth, bvExpr, proof, expr⟩
    | BitVec.signExtend _ newWidthExpr innerExpr =>
      let some newWidth ← getNatValue? newWidthExpr | return none
      let some inner ← goOrAtom innerExpr | return none
      let bvExpr := .signExtend newWidth inner.bvExpr
      let expr :=
        mkApp3
          (mkConst ``BVExpr.signExtend)
          (toExpr inner.width)
          newWidthExpr
          inner.expr
      let proof := do
        let innerEval ← ReifiedBVExpr.mkEvalExpr inner.width inner.expr
        let innerProof ← inner.evalsAtAtoms
        return mkApp5 (mkConst ``Std.Tactic.BVDecide.Reflect.BitVec.signExtend_congr)
          newWidthExpr
          (toExpr inner.width)
          innerExpr
          innerEval
          innerProof
      return some ⟨newWidth, bvExpr, proof, expr⟩
    | HAppend.hAppend _ _ _ _ lhsExpr rhsExpr =>
      let some lhs ← goOrAtom lhsExpr | return none
      let some rhs ← goOrAtom rhsExpr | return none
      let bvExpr := .append lhs.bvExpr rhs.bvExpr
      let expr := mkApp4 (mkConst ``BVExpr.append)
        (toExpr lhs.width)
        (toExpr rhs.width)
        lhs.expr rhs.expr
      let proof := do
        let lhsEval ← ReifiedBVExpr.mkEvalExpr lhs.width lhs.expr
        let lhsProof ← lhs.evalsAtAtoms
        let rhsProof ← rhs.evalsAtAtoms
        let rhsEval ← ReifiedBVExpr.mkEvalExpr rhs.width rhs.expr
        return mkApp8 (mkConst ``Std.Tactic.BVDecide.Reflect.BitVec.append_congr)
          (toExpr lhs.width) (toExpr rhs.width)
          lhsExpr lhsEval
          rhsExpr rhsEval
          lhsProof rhsProof
      return some ⟨lhs.width + rhs.width, bvExpr, proof, expr⟩
    | BitVec.replicate _ nExpr innerExpr =>
      let some inner ← goOrAtom innerExpr | return none
      let some n ← getNatValue? nExpr | return none
      let bvExpr := .replicate n inner.bvExpr
      let expr := mkApp3 (mkConst ``BVExpr.replicate)
        (toExpr inner.width)
        (toExpr n)
        inner.expr
      let proof := do
        let innerEval ← ReifiedBVExpr.mkEvalExpr inner.width inner.expr
        let innerProof ← inner.evalsAtAtoms
        return mkApp5 (mkConst ``Std.Tactic.BVDecide.Reflect.BitVec.replicate_congr)
          (toExpr n)
          (toExpr inner.width)
          innerExpr
          innerEval
          innerProof
      return some ⟨inner.width * n, bvExpr, proof, expr⟩
    | BitVec.extractLsb' _ startExpr lenExpr innerExpr =>
      let some start ← getNatValue? startExpr | return none
      let some len ← getNatValue? lenExpr | return none
      let some inner ← goOrAtom innerExpr | return none
      let bvExpr := .extract start len inner.bvExpr
      let expr := mkApp4 (mkConst ``BVExpr.extract)
        (toExpr inner.width)
        startExpr
        lenExpr
        inner.expr
      let proof := do
        let innerEval ← ReifiedBVExpr.mkEvalExpr inner.width inner.expr
        let innerProof ← inner.evalsAtAtoms
        return mkApp6 (mkConst ``Std.Tactic.BVDecide.Reflect.BitVec.extract_congr)
          startExpr
          lenExpr
          (toExpr inner.width)
          innerExpr
          innerEval
          innerProof
      return some ⟨len, bvExpr, proof, expr⟩
    | BitVec.rotateLeft _ innerExpr distanceExpr =>
      rotateReflection
        distanceExpr
        innerExpr
        .rotateLeft
        ``BVUnOp.rotateLeft
        ``Std.Tactic.BVDecide.Reflect.BitVec.rotateLeft_congr
    | BitVec.rotateRight _ innerExpr distanceExpr =>
      rotateReflection
        distanceExpr
        innerExpr
        .rotateRight
        ``BVUnOp.rotateRight
        ``Std.Tactic.BVDecide.Reflect.BitVec.rotateRight_congr
    | ite _ discrExpr _ lhsExpr rhsExpr =>
      let_expr Eq α discrExpr val := discrExpr | return none
      let_expr Bool := α | return none
      let_expr Bool.true := val | return none
      let some atom ← ReifiedBVExpr.bitVecAtom x true | return none
      let some discr ← ReifiedBVLogical.of discrExpr | return none
      let some lhs ← goOrAtom lhsExpr | return none
      let some rhs ← goOrAtom rhsExpr | return none
      addIfLemmas discr atom lhs rhs discrExpr x lhsExpr rhsExpr
      return some atom
    | _ => return none

  /--
  Reify `x` or abstract it as an atom.
  Unless this function is called on something that is not a fixed-width `BitVec` it is always going
  to return `some`.
  -/
  goOrAtom (x : Expr) : LemmaM (Option ReifiedBVExpr) := do
    let res ← go x
    match res with
    | some exp => return some exp
    | none => ReifiedBVExpr.bitVecAtom x false

  shiftConstLikeReflection (distance : Nat) (innerExpr : Expr) (shiftOp : Nat → BVUnOp)
      (shiftOpName : Name) (congrThm : Name) :
      LemmaM (Option ReifiedBVExpr) := do
    let some inner ← goOrAtom innerExpr | return none
    let bvExpr : BVExpr inner.width := .un (shiftOp distance) inner.bvExpr
    let expr :=
      mkApp3
        (mkConst ``BVExpr.un)
        (toExpr inner.width)
        (mkApp (mkConst shiftOpName) (toExpr distance))
        inner.expr
    let congrProof :=
      mkApp
        (mkConst congrThm)
        (toExpr distance)
    let proof := unaryCongrProof inner innerExpr congrProof
    return some ⟨inner.width, bvExpr, proof, expr⟩

  rotateReflection (distanceExpr : Expr) (innerExpr : Expr) (rotateOp : Nat → BVUnOp)
      (rotateOpName : Name) (congrThm : Name) :
      LemmaM (Option ReifiedBVExpr) := do
    let some distance ← getNatValue? distanceExpr | return none
    shiftConstLikeReflection distance innerExpr rotateOp rotateOpName congrThm

  shiftConstReflection (β : Expr) (distanceExpr : Expr) (innerExpr : Expr) (shiftOp : Nat → BVUnOp)
      (shiftOpName : Name) (congrThm : Name) :
      LemmaM (Option ReifiedBVExpr) := do
    let some distance ← ReifiedBVExpr.getNatOrBvValue? β distanceExpr | return none
    shiftConstLikeReflection distance innerExpr shiftOp shiftOpName congrThm

  shiftReflection (distanceExpr : Expr) (innerExpr : Expr)
      (shiftOp : {m n : Nat} → BVExpr m → BVExpr n → BVExpr m) (shiftOpName : Name)
      (congrThm : Name) :
      LemmaM (Option ReifiedBVExpr) := do
    let some inner ← goOrAtom innerExpr | return none
    let some distance ← goOrAtom distanceExpr | return none
    let bvExpr : BVExpr inner.width := shiftOp inner.bvExpr distance.bvExpr
    let expr :=
      mkApp4
        (mkConst shiftOpName)
        (toExpr inner.width)
        (toExpr distance.width)
        inner.expr
        distance.expr
    let congrProof :=
      mkApp2
        (mkConst congrThm)
        (toExpr inner.width)
        (toExpr distance.width)
    let proof := binaryCongrProof inner distance innerExpr distanceExpr congrProof
    return some ⟨inner.width, bvExpr, proof, expr⟩

  binaryReflection (lhsExpr rhsExpr : Expr) (op : BVBinOp) (congrThm : Name) :
      LemmaM (Option ReifiedBVExpr) := do
    let some lhs ← goOrAtom lhsExpr | return none
    let some rhs ← goOrAtom rhsExpr | return none
    if h : rhs.width = lhs.width then
      let bvExpr : BVExpr lhs.width := .bin lhs.bvExpr op (h ▸ rhs.bvExpr)
      let expr := mkApp4 (mkConst ``BVExpr.bin) (toExpr lhs.width) lhs.expr (toExpr op) rhs.expr
      let congrThm := mkApp (mkConst congrThm) (toExpr lhs.width)
      let proof := binaryCongrProof lhs rhs lhsExpr rhsExpr congrThm
      return some ⟨lhs.width, bvExpr, proof, expr⟩
    else
      return none

  binaryCongrProof (lhs rhs : ReifiedBVExpr) (lhsExpr rhsExpr : Expr) (congrThm : Expr) :
      M Expr := do
    let lhsEval ← ReifiedBVExpr.mkEvalExpr lhs.width lhs.expr
    let lhsProof ← lhs.evalsAtAtoms
    let rhsProof ← rhs.evalsAtAtoms
    let rhsEval ← ReifiedBVExpr.mkEvalExpr rhs.width rhs.expr
    return mkApp6 congrThm lhsExpr rhsExpr lhsEval rhsEval lhsProof rhsProof

  unaryReflection (innerExpr : Expr) (op : BVUnOp) (congrThm : Name) :
      LemmaM (Option ReifiedBVExpr) := do
    let some inner ← goOrAtom innerExpr | return none
    let bvExpr := .un op inner.bvExpr
    let expr := mkApp3 (mkConst ``BVExpr.un) (toExpr inner.width) (toExpr op) inner.expr
    let proof := unaryCongrProof inner innerExpr (mkConst congrThm)
    return some ⟨inner.width, bvExpr, proof, expr⟩

  unaryCongrProof (inner : ReifiedBVExpr) (innerExpr : Expr) (congrProof : Expr) : M Expr := do
    let innerEval ← ReifiedBVExpr.mkEvalExpr inner.width inner.expr
    let innerProof ← inner.evalsAtAtoms
    return mkApp4 congrProof (toExpr inner.width) innerExpr innerEval innerProof

  goBvLit (x : Expr) : M (Option ReifiedBVExpr) := do
    let some ⟨_, bvVal⟩ ← getBitVecValue? x | return ← ReifiedBVExpr.bitVecAtom x false
    ReifiedBVExpr.mkBVConst bvVal

/--
Reify an `Expr` that is a predicate about `BitVec`.
Unless this function is called on something that is not a `Bool` it is always going to return `some`.
-/
partial def ReifiedBVPred.of (t : Expr) : LemmaM (Option ReifiedBVPred) := do
  match ← go t with
  | some pred => return some pred
  | none => ReifiedBVPred.boolAtom t
where
  /--
  Reify `t`, returns `none` if the reification procedure failed.
  -/
  go (t : Expr) : LemmaM (Option ReifiedBVPred) := do
    match_expr t with
    | BEq.beq α _ lhsExpr rhsExpr =>
      let_expr BitVec _ := α | return none
      binaryReflection lhsExpr rhsExpr .eq
    | BitVec.ult _ lhsExpr rhsExpr =>
      binaryReflection lhsExpr rhsExpr .ult
    | BitVec.getLsbD _ subExpr idxExpr =>
      let some sub ← ReifiedBVExpr.of subExpr | return none
      let some idx ← getNatValue? idxExpr | return none
      return some (← ReifiedBVPred.mkGetLsbD sub subExpr idx)
    | _ => return none

  binaryReflection (lhsExpr rhsExpr : Expr) (pred : BVBinPred) : LemmaM (Option ReifiedBVPred) := do
    let some lhs ← ReifiedBVExpr.of lhsExpr | return none
    let some rhs ← ReifiedBVExpr.of rhsExpr | return none
    ReifiedBVPred.mkBinPred lhs rhs lhsExpr rhsExpr pred

/--
Reify an `Expr` that is a boolean expression containing predicates about `BitVec` as atoms.
Unless this function is called on something that is not a `Bool` it is always going to return `some`.
-/
partial def ReifiedBVLogical.of (t : Expr) : LemmaM (Option ReifiedBVLogical) := do
  goOrAtom t
where
  /--
  Reify `t`, returns `none` if the reification procedure failed.
  -/
  go (t : Expr) : LemmaM (Option ReifiedBVLogical) := do
    match_expr t with
    | Bool.true => ReifiedBVLogical.mkBoolConst true
    | Bool.false => ReifiedBVLogical.mkBoolConst false
    | Bool.not subExpr =>
      let some sub ← goOrAtom subExpr | return none
      return some (← ReifiedBVLogical.mkNot sub subExpr)
    | Bool.and lhsExpr rhsExpr => gateReflection lhsExpr rhsExpr .and
    | Bool.xor lhsExpr rhsExpr => gateReflection lhsExpr rhsExpr .xor
    | BEq.beq α _ lhsExpr rhsExpr =>
      match_expr α with
      | Bool => gateReflection lhsExpr rhsExpr .beq
      | BitVec _ => goPred t
      | _ => return none
    | ite _ discrExpr _ lhsExpr rhsExpr =>
      let_expr Eq α discrExpr val := discrExpr | return none
      let_expr Bool := α | return none
      let_expr Bool.true := val | return none
      let some discr ← goOrAtom discrExpr | return none
      let some lhs ← goOrAtom lhsExpr | return none
      let some rhs ← goOrAtom rhsExpr | return none
      return some (← ReifiedBVLogical.mkIte discr lhs rhs discrExpr lhsExpr rhsExpr)
    | _ => goPred t

  /--
  Reify `t` or abstract it as an atom.
  Unless this function is called on something that is not a `Bool` it is always going to return `some`.
  -/
  goOrAtom (t : Expr) : LemmaM (Option ReifiedBVLogical) := do
    match ← go t with
    | some boolExpr => return some boolExpr
    | none => ReifiedBVLogical.boolAtom t

  gateReflection (lhsExpr rhsExpr : Expr) (gate : Gate) :
      LemmaM (Option ReifiedBVLogical) := do
    let some lhs ← goOrAtom lhsExpr | return none
    let some rhs ← goOrAtom rhsExpr | return none
    ReifiedBVLogical.mkGate lhs rhs lhsExpr rhsExpr gate

  goPred (t : Expr) : LemmaM (Option ReifiedBVLogical) := do
    let some pred ← ReifiedBVPred.of t | return none
    ReifiedBVLogical.ofPred pred

end

end Frontend
end Lean.Elab.Tactic.BVDecide
