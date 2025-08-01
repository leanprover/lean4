/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean.Elab.Tactic.BVDecide.Frontend.BVDecide.ReifiedBVLogical
public import Lean.Elab.Tactic.BVDecide.Frontend.BVDecide.ReifiedLemmas

public section

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
partial def ReifiedBVExpr.of (origExpr : Expr) : LemmaM (Option ReifiedBVExpr) := do
  goOrAtom origExpr
where
  /--
  Reify `x`, returns `none` if the reification procedure failed.
  -/
  go (origExpr : Expr) : LemmaM (Option ReifiedBVExpr) := do
    match_expr origExpr with
    | BitVec.ofNat _ _ => goBvLit origExpr
    | HAnd.hAnd _ _ _ _ lhsExpr rhsExpr =>
      binaryReflection lhsExpr rhsExpr .and ``Std.Tactic.BVDecide.Reflect.BitVec.and_congr origExpr
    | HXor.hXor _ _ _ _ lhsExpr rhsExpr =>
      binaryReflection lhsExpr rhsExpr .xor ``Std.Tactic.BVDecide.Reflect.BitVec.xor_congr origExpr
    | HAdd.hAdd _ _ _ _ lhsExpr rhsExpr =>
      binaryReflection lhsExpr rhsExpr .add ``Std.Tactic.BVDecide.Reflect.BitVec.add_congr origExpr
    | HMul.hMul _ _ _ _ lhsExpr rhsExpr =>
      binaryReflection lhsExpr rhsExpr .mul ``Std.Tactic.BVDecide.Reflect.BitVec.mul_congr origExpr
    | HDiv.hDiv _ _ _ _ lhsExpr rhsExpr =>
      binaryReflection lhsExpr rhsExpr .udiv ``Std.Tactic.BVDecide.Reflect.BitVec.udiv_congr origExpr
    | HMod.hMod _ _ _ _ lhsExpr rhsExpr =>
      binaryReflection lhsExpr rhsExpr .umod ``Std.Tactic.BVDecide.Reflect.BitVec.umod_congr origExpr
    | Complement.complement _ _ innerExpr =>
      unaryReflection innerExpr .not ``Std.Tactic.BVDecide.Reflect.BitVec.not_congr origExpr
    | HShiftLeft.hShiftLeft α β _ _ innerExpr distanceExpr =>
      let distance? ← ReifiedBVExpr.getNatOrBvValue? β distanceExpr
      let_expr BitVec wExpr := α | return none
      if (← getNatValue? wExpr).isSome && distance?.isSome then
        throwError "internal error: constant shift should have been eliminated."
      let_expr BitVec _ := β | return none
      shiftReflection
        distanceExpr
        innerExpr
        .shiftLeft
        ``BVExpr.shiftLeft
        ``Std.Tactic.BVDecide.Reflect.BitVec.shiftLeft_congr
        origExpr
    | HShiftRight.hShiftRight α β _ _ innerExpr distanceExpr =>
      let distance? ← ReifiedBVExpr.getNatOrBvValue? β distanceExpr
      let_expr BitVec wExpr := α | return none
      if (← getNatValue? wExpr).isSome && distance?.isSome then
        throwError "internal error: constant shift should have been eliminated."
      let_expr BitVec _ := β | return none
      shiftReflection
        distanceExpr
        innerExpr
        .shiftRight
        ``BVExpr.shiftRight
        ``Std.Tactic.BVDecide.Reflect.BitVec.shiftRight_congr
        origExpr
    | BitVec.sshiftRight _ innerExpr distanceExpr =>
      let some distance ← getNatValue? distanceExpr | return none
      shiftConstLikeReflection
        distance
        innerExpr
        .arithShiftRightConst
        ``BVUnOp.arithShiftRightConst
        ``Std.Tactic.BVDecide.Reflect.BitVec.arithShiftRightNat_congr
        origExpr
    | BitVec.sshiftRight' _ _ innerExpr distanceExpr =>
      shiftReflection
        distanceExpr
        innerExpr
        .arithShiftRight
        ``BVExpr.arithShiftRight
        ``Std.Tactic.BVDecide.Reflect.BitVec.arithShiftRight_congr
        origExpr
    | HAppend.hAppend _ _ _ _ lhsExpr rhsExpr =>
      let some lhs ← goOrAtom lhsExpr | return none
      let some rhs ← goOrAtom rhsExpr | return none
      let bvExpr := .append lhs.bvExpr rhs.bvExpr rfl
      let wExpr := toExpr (lhs.width + rhs.width)
      let expr :=
        mkApp6 (mkConst ``BVExpr.append)
          (toExpr lhs.width)
          (toExpr rhs.width)
          wExpr
          lhs.expr
          rhs.expr
          (← mkEqRefl wExpr)
      let proof := do
        let lhsEval ← ReifiedBVExpr.mkEvalExpr lhs.width lhs.expr
        let rhsEval ← ReifiedBVExpr.mkEvalExpr rhs.width rhs.expr
        let lhsProof? ← lhs.evalsAtAtoms
        let rhsProof? ← rhs.evalsAtAtoms
        let some (lhsProof, rhsProof) :=
          M.simplifyBinaryProof'
            (ReifiedBVExpr.mkBVRefl lhs.width) lhsEval lhsProof?
            (ReifiedBVExpr.mkBVRefl rhs.width) rhsEval rhsProof? | return none
        return mkApp8 (mkConst ``Std.Tactic.BVDecide.Reflect.BitVec.append_congr)
          (toExpr lhs.width) (toExpr rhs.width)
          lhsExpr lhsEval
          rhsExpr rhsEval
          lhsProof rhsProof
      return some ⟨lhs.width + rhs.width, bvExpr, origExpr, proof, expr⟩
    | BitVec.replicate _ nExpr innerExpr =>
      let some inner ← goOrAtom innerExpr | return none
      let some n ← getNatValue? nExpr | return none
      let bvExpr := .replicate n inner.bvExpr rfl
      let newWExpr := toExpr (inner.width * n)
      let expr :=
        mkApp5 (mkConst ``BVExpr.replicate)
          (toExpr inner.width)
          newWExpr
          (toExpr n)
          inner.expr
          (← mkEqRefl newWExpr)
      let proof := do
        let innerEval ← ReifiedBVExpr.mkEvalExpr inner.width inner.expr
        -- This is safe as `replicate_congr` holds definitionally if the arguments are defeq.
        let some innerProof ← inner.evalsAtAtoms | return none
        return mkApp5 (mkConst ``Std.Tactic.BVDecide.Reflect.BitVec.replicate_congr)
          (toExpr n)
          (toExpr inner.width)
          innerExpr
          innerEval
          innerProof
      return some ⟨inner.width * n, bvExpr, origExpr, proof, expr⟩
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
        -- This is safe as `extract_congr` holds definitionally if the arguments are defeq.
        let some innerProof ← inner.evalsAtAtoms | return none
        return mkApp6 (mkConst ``Std.Tactic.BVDecide.Reflect.BitVec.extract_congr)
          startExpr
          lenExpr
          (toExpr inner.width)
          innerExpr
          innerEval
          innerProof
      return some ⟨len, bvExpr, origExpr, proof, expr⟩
    | BitVec.rotateLeft _ innerExpr distanceExpr =>
      rotateReflection
        distanceExpr
        innerExpr
        .rotateLeft
        ``BVUnOp.rotateLeft
        ``Std.Tactic.BVDecide.Reflect.BitVec.rotateLeft_congr
        origExpr
    | BitVec.rotateRight _ innerExpr distanceExpr =>
      rotateReflection
        distanceExpr
        innerExpr
        .rotateRight
        ``BVUnOp.rotateRight
        ``Std.Tactic.BVDecide.Reflect.BitVec.rotateRight_congr
        origExpr
    | cond _ discrExpr lhsExpr rhsExpr =>
      let some atom ← ReifiedBVExpr.bitVecAtom origExpr true | return none
      let some discr ← ReifiedBVLogical.of discrExpr | return none
      let some lhs ← goOrAtom lhsExpr | return none
      let some rhs ← goOrAtom rhsExpr | return none
      addCondLemmas discr atom lhs rhs discrExpr origExpr lhsExpr rhsExpr
      return some atom
    | BitVec.reverse _ innerExpr =>
      unaryReflection innerExpr .reverse ``Std.Tactic.BVDecide.Reflect.BitVec.reverse_congr origExpr
    | BitVec.clz _ innerExpr =>
      unaryReflection innerExpr .clz ``Std.Tactic.BVDecide.Reflect.BitVec.clz_congr origExpr
    | _ => return none

  /--
  Reify `origExpr` or abstract it as an atom.
  Unless this function is called on something that is not a fixed-width `BitVec` it is always going
  to return `some`.
  -/
  goOrAtom (origExpr : Expr) : LemmaM (Option ReifiedBVExpr) := do
    LemmaM.withBVExprCache origExpr fun origExpr => do
      let res ← go origExpr
      match res with
      | some exp => return some exp
      | none => ReifiedBVExpr.bitVecAtom origExpr false

  shiftConstLikeReflection (distance : Nat) (innerExpr : Expr) (shiftOp : Nat → BVUnOp)
      (shiftOpName : Name) (congrThm : Name) (origExpr : Expr) :
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
    return some ⟨inner.width, bvExpr, origExpr, proof, expr⟩

  rotateReflection (distanceExpr : Expr) (innerExpr : Expr) (rotateOp : Nat → BVUnOp)
      (rotateOpName : Name) (congrThm : Name) (origExpr : Expr) :
      LemmaM (Option ReifiedBVExpr) := do
    let some distance ← getNatValue? distanceExpr | return none
    shiftConstLikeReflection distance innerExpr rotateOp rotateOpName congrThm origExpr

  shiftReflection (distanceExpr : Expr) (innerExpr : Expr)
      (shiftOp : {m n : Nat} → BVExpr m → BVExpr n → BVExpr m) (shiftOpName : Name)
      (congrThm : Name) (origExpr : Expr) :
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
    return some ⟨inner.width, bvExpr, origExpr, proof, expr⟩

  binaryReflection (lhsExpr rhsExpr : Expr) (op : BVBinOp) (congrThm : Name) (origExpr : Expr) :
      LemmaM (Option ReifiedBVExpr) := do
    let some lhs ← goOrAtom lhsExpr | return none
    let some rhs ← goOrAtom rhsExpr | return none
    if h : rhs.width = lhs.width then
      let bvExpr : BVExpr lhs.width := .bin lhs.bvExpr op (h ▸ rhs.bvExpr)
      let expr := mkApp4 (mkConst ``BVExpr.bin) (toExpr lhs.width) lhs.expr (toExpr op) rhs.expr
      let congrThm := mkApp (mkConst congrThm) (toExpr lhs.width)
      let proof := binaryCongrProof lhs rhs lhsExpr rhsExpr congrThm
      return some ⟨lhs.width, bvExpr, origExpr, proof, expr⟩
    else
      return none

  binaryCongrProof (lhs rhs : ReifiedBVExpr) (lhsExpr rhsExpr : Expr) (congrThm : Expr) :
      M (Option Expr) := do
    let lhsEval ← ReifiedBVExpr.mkEvalExpr lhs.width lhs.expr
    let rhsEval ← ReifiedBVExpr.mkEvalExpr rhs.width rhs.expr
    let lhsProof? ← lhs.evalsAtAtoms
    let rhsProof? ← rhs.evalsAtAtoms
    let some (lhsProof, rhsProof) :=
      M.simplifyBinaryProof
        (ReifiedBVExpr.mkBVRefl lhs.width)
        lhsEval lhsProof?
        rhsEval rhsProof? | return none
    return mkApp6 congrThm lhsExpr rhsExpr lhsEval rhsEval lhsProof rhsProof

  unaryReflection (innerExpr : Expr) (op : BVUnOp) (congrThm : Name) (origExpr : Expr) :
      LemmaM (Option ReifiedBVExpr) := do
    let some inner ← goOrAtom innerExpr | return none
    let bvExpr := .un op inner.bvExpr
    let expr := mkApp3 (mkConst ``BVExpr.un) (toExpr inner.width) (toExpr op) inner.expr
    let proof := unaryCongrProof inner innerExpr (mkConst congrThm)
    return some ⟨inner.width, bvExpr, origExpr, proof, expr⟩

  unaryCongrProof (inner : ReifiedBVExpr) (innerExpr : Expr) (congrProof : Expr) : M (Option Expr) := do
    let innerEval ← ReifiedBVExpr.mkEvalExpr inner.width inner.expr
    let some innerProof ← inner.evalsAtAtoms | return none
    return mkApp4 congrProof (toExpr inner.width) innerExpr innerEval innerProof

  goBvLit (x : Expr) : M (Option ReifiedBVExpr) := do
    let some ⟨_, bvVal⟩ ← getBitVecValue? x | return ← ReifiedBVExpr.bitVecAtom x false
    ReifiedBVExpr.mkBVConst bvVal

/--
Reify an `Expr` that is a predicate about `BitVec`.
Unless this function is called on something that is not a `Bool` it is always going to return `some`.
-/
partial def ReifiedBVPred.of (origExpr : Expr) : LemmaM (Option ReifiedBVPred) := do
  LemmaM.withBVPredCache origExpr fun origExpr => do
    match ← go origExpr with
    | some pred => return some pred
    | none => ReifiedBVPred.boolAtom origExpr
where
  /--
  Reify `origExpr`, returns `none` if the reification procedure failed.
  -/
  go (origExpr : Expr) : LemmaM (Option ReifiedBVPred) := do
    match_expr origExpr with
    | BEq.beq α _ lhsExpr rhsExpr =>
      let_expr BitVec _ := α | return none
      binaryReflection lhsExpr rhsExpr .eq origExpr
    | BitVec.ult _ lhsExpr rhsExpr =>
      binaryReflection lhsExpr rhsExpr .ult origExpr
    | BitVec.getLsbD _ subExpr idxExpr =>
      let some sub ← ReifiedBVExpr.of subExpr | return none
      let some idx ← getNatValue? idxExpr | return none
      return some (← ReifiedBVPred.mkGetLsbD sub subExpr idx origExpr)
    | _ => return none

  binaryReflection (lhsExpr rhsExpr : Expr) (pred : BVBinPred) (origExpr : Expr) :
      LemmaM (Option ReifiedBVPred) := do
    let some lhs ← ReifiedBVExpr.of lhsExpr | return none
    let some rhs ← ReifiedBVExpr.of rhsExpr | return none
    ReifiedBVPred.mkBinPred lhs rhs lhsExpr rhsExpr pred origExpr

/--
Reify an `Expr` that is a boolean expression containing predicates about `BitVec` as atoms.
Unless this function is called on something that is not a `Bool` it is always going to return `some`.
-/
partial def ReifiedBVLogical.of (origExpr : Expr) : LemmaM (Option ReifiedBVLogical) := do
  goOrAtom origExpr
where
  /--
  Reify `t`, returns `none` if the reification procedure failed.
  -/
  go (origExpr : Expr) : LemmaM (Option ReifiedBVLogical) := do
    match_expr origExpr with
    | Bool.true => ReifiedBVLogical.mkBoolConst true
    | Bool.false => ReifiedBVLogical.mkBoolConst false
    | Bool.not subExpr =>
      let some sub ← goOrAtom subExpr | return none
      return some (← ReifiedBVLogical.mkNot sub subExpr origExpr)
    | Bool.and lhsExpr rhsExpr => gateReflection lhsExpr rhsExpr .and origExpr
    | Bool.xor lhsExpr rhsExpr => gateReflection lhsExpr rhsExpr .xor origExpr
    | BEq.beq α _ lhsExpr rhsExpr =>
      match_expr α with
      | Bool => gateReflection lhsExpr rhsExpr .beq origExpr
      | BitVec _ => goPred origExpr
      | _ => return none
    | cond _ discrExpr lhsExpr rhsExpr =>
      let some discr ← goOrAtom discrExpr | return none
      let some lhs ← goOrAtom lhsExpr | return none
      let some rhs ← goOrAtom rhsExpr | return none
      return some (← ReifiedBVLogical.mkIte discr lhs rhs discrExpr lhsExpr rhsExpr origExpr)
    | _ => goPred origExpr

  /--
  Reify `t` or abstract it as an atom.
  Unless this function is called on something that is not a `Bool` it is always going to return `some`.
  -/
  goOrAtom (origExpr : Expr) : LemmaM (Option ReifiedBVLogical) := do
    LemmaM.withBVLogicalCache origExpr fun origExpr => do
      match ← go origExpr with
      | some boolExpr => return some boolExpr
      | none => ReifiedBVLogical.boolAtom origExpr

  gateReflection (lhsExpr rhsExpr : Expr) (gate : Gate) (origExpr : Expr) :
      LemmaM (Option ReifiedBVLogical) := do
    let some lhs ← goOrAtom lhsExpr | return none
    let some rhs ← goOrAtom rhsExpr | return none
    ReifiedBVLogical.mkGate lhs rhs lhsExpr rhsExpr gate origExpr

  goPred (origExpr : Expr) : LemmaM (Option ReifiedBVLogical) := do
    let some pred ← ReifiedBVPred.of origExpr | return none
    ReifiedBVLogical.ofPred pred

end

end Frontend
end Lean.Elab.Tactic.BVDecide
