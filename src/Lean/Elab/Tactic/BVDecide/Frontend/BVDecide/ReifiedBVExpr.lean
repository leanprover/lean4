/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Lean.Elab.Tactic.BVDecide.Frontend.BVDecide.Reflect
import Std.Tactic.BVDecide.Reflect

/-!
Provides the logic for reifying `BitVec` expressions.
-/

namespace Lean.Elab.Tactic.BVDecide
namespace Frontend

open Lean.Meta
open Std.Tactic.BVDecide
open Std.Tactic.BVDecide.Reflect.BitVec

/--
A reified version of an `Expr` representing a `BVExpr`.
-/
structure ReifiedBVExpr where
  width : Nat
  /--
  The reified expression.
  -/
  bvExpr : BVExpr width
  /--
  A proof that `bvExpr.eval atomsAssignment = originalBVExpr`.
  -/
  evalsAtAtoms : M Expr
  /--
  A cache for `toExpr bvExpr`.
  -/
  expr : Expr

namespace ReifiedBVExpr

def mkEvalExpr (w : Nat) (expr : Expr) : M Expr := do
  return mkApp3 (mkConst ``BVExpr.eval) (toExpr w) (← M.atomsAssignment) expr

def mkBVRefl (w : Nat) (expr : Expr) : Expr :=
  mkApp2
   (mkConst ``Eq.refl [1])
   (mkApp (mkConst ``BitVec) (toExpr w))
   expr

def mkAtom (e : Expr) (width : Nat) : M ReifiedBVExpr := do
  let ident ← M.lookup e width
  let expr := mkApp2 (mkConst ``BVExpr.var) (toExpr width) (toExpr ident)
  let proof := do
    let evalExpr ← mkEvalExpr width expr
    return mkBVRefl width evalExpr
  return ⟨width, .var ident, proof, expr⟩

def getNatOrBvValue? (ty : Expr) (expr : Expr) : M (Option Nat) := do
  match_expr ty with
  | Nat =>
    getNatValue? expr
  | BitVec _ =>
    let some ⟨_, distance⟩ ← getBitVecValue? expr | return none
    return some distance.toNat
  | _ => return none

/--
Reify an `Expr` that's a `BitVec`.
-/
partial def of (x : Expr) : M (Option ReifiedBVExpr) := do
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
  | Complement.complement _ _ innerExpr =>
    unaryReflection innerExpr .not ``Std.Tactic.BVDecide.Reflect.BitVec.not_congr
  | HShiftLeft.hShiftLeft _ β _ _ innerExpr distanceExpr =>
    let distance? ← getNatOrBvValue? β distanceExpr
    if distance?.isSome then
      shiftConstReflection
        β
        distanceExpr
        innerExpr
        .shiftLeftConst
        ``BVUnOp.shiftLeftConst
        ``Std.Tactic.BVDecide.Reflect.BitVec.shiftLeftNat_congr
    else
      shiftReflection
        β
        distanceExpr
        innerExpr
        .shiftLeft
        ``BVExpr.shiftLeft
        ``Std.Tactic.BVDecide.Reflect.BitVec.shiftLeft_congr
  | HShiftRight.hShiftRight _ β _ _ innerExpr distanceExpr =>
    let distance? ← getNatOrBvValue? β distanceExpr
    if distance?.isSome then
      shiftConstReflection
        β
        distanceExpr
        innerExpr
        .shiftRightConst
        ``BVUnOp.shiftRightConst
        ``Std.Tactic.BVDecide.Reflect.BitVec.shiftRightNat_congr
    else
      shiftReflection
        β
        distanceExpr
        innerExpr
        .shiftRight
        ``BVExpr.shiftRight
        ``Std.Tactic.BVDecide.Reflect.BitVec.shiftRight_congr
  | BitVec.sshiftRight _ innerExpr distanceExpr =>
    let some distance ← getNatValue? distanceExpr | return ← ofAtom x
    shiftConstLikeReflection
      distance
      innerExpr
      .arithShiftRightConst
      ``BVUnOp.arithShiftRightConst
      ``Std.Tactic.BVDecide.Reflect.BitVec.arithShiftRight_congr
  | BitVec.zeroExtend _ newWidthExpr innerExpr =>
    let some newWidth ← getNatValue? newWidthExpr | return ← ofAtom x
    let some inner ← ofOrAtom innerExpr | return none
    let bvExpr := .zeroExtend newWidth inner.bvExpr
    let expr :=
      mkApp3
        (mkConst ``BVExpr.zeroExtend)
        (toExpr inner.width)
        newWidthExpr
        inner.expr
    let proof := do
      let innerEval ← mkEvalExpr inner.width inner.expr
      let innerProof ← inner.evalsAtAtoms
      return mkApp5 (mkConst ``Std.Tactic.BVDecide.Reflect.BitVec.zeroExtend_congr)
        newWidthExpr
        (toExpr inner.width)
        innerExpr
        innerEval
        innerProof
    return some ⟨newWidth, bvExpr, proof, expr⟩
  | BitVec.signExtend _ newWidthExpr innerExpr =>
    let some newWidth ← getNatValue? newWidthExpr | return ← ofAtom x
    let some inner ← ofOrAtom innerExpr | return none
    let bvExpr := .signExtend newWidth inner.bvExpr
    let expr :=
      mkApp3
        (mkConst ``BVExpr.signExtend)
        (toExpr inner.width)
        newWidthExpr
        inner.expr
    let proof := do
      let innerEval ← mkEvalExpr inner.width inner.expr
      let innerProof ← inner.evalsAtAtoms
      return mkApp5 (mkConst ``Std.Tactic.BVDecide.Reflect.BitVec.signExtend_congr)
        newWidthExpr
        (toExpr inner.width)
        innerExpr
        innerEval
        innerProof
    return some ⟨newWidth, bvExpr, proof, expr⟩
  | HAppend.hAppend _ _ _ _ lhsExpr rhsExpr =>
    let some lhs ← ofOrAtom lhsExpr | return none
    let some rhs ← ofOrAtom rhsExpr | return none
    let bvExpr := .append lhs.bvExpr rhs.bvExpr
    let expr := mkApp4 (mkConst ``BVExpr.append)
      (toExpr lhs.width)
      (toExpr rhs.width)
      lhs.expr rhs.expr
    let proof := do
      let lhsEval ← mkEvalExpr lhs.width lhs.expr
      let lhsProof ← lhs.evalsAtAtoms
      let rhsProof ← rhs.evalsAtAtoms
      let rhsEval ← mkEvalExpr rhs.width rhs.expr
      return mkApp8 (mkConst ``Std.Tactic.BVDecide.Reflect.BitVec.append_congr)
        (toExpr lhs.width) (toExpr rhs.width)
        lhsExpr lhsEval
        rhsExpr rhsEval
        lhsProof rhsProof
    return some ⟨lhs.width + rhs.width, bvExpr, proof, expr⟩
  | BitVec.replicate _ nExpr innerExpr =>
    let some inner ← ofOrAtom innerExpr | return none
    let some n ← getNatValue? nExpr | return ← ofAtom x
    let bvExpr := .replicate n inner.bvExpr
    let expr := mkApp3 (mkConst ``BVExpr.replicate)
      (toExpr inner.width)
      (toExpr n)
      inner.expr
    let proof := do
      let innerEval ← mkEvalExpr inner.width inner.expr
      let innerProof ← inner.evalsAtAtoms
      return mkApp5 (mkConst ``Std.Tactic.BVDecide.Reflect.BitVec.replicate_congr)
        (toExpr n)
        (toExpr inner.width)
        innerExpr
        innerEval
        innerProof
    return some ⟨inner.width * n, bvExpr, proof, expr⟩
  | BitVec.extractLsb' _ startExpr lenExpr innerExpr =>
    let some start ← getNatValue? startExpr | return ← ofAtom x
    let some len ← getNatValue? lenExpr | return ← ofAtom x
    let some inner ← ofOrAtom innerExpr | return none
    let bvExpr := .extract start len inner.bvExpr
    let expr := mkApp4 (mkConst ``BVExpr.extract)
      (toExpr inner.width)
      startExpr
      lenExpr
      inner.expr
    let proof := do
      let innerEval ← mkEvalExpr inner.width inner.expr
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
  | _ => ofAtom x
where
  ofAtom (x : Expr) : M (Option ReifiedBVExpr) := do
    let t ← instantiateMVars (← whnfR (← inferType x))
    let_expr BitVec widthExpr := t | return none
    let some width ← getNatValue? widthExpr | return none
    let atom ← mkAtom x width
    return some atom

  ofOrAtom (x : Expr) : M (Option ReifiedBVExpr) := do
    let res ← of x
    match res with
    | some exp => return some exp
    | none => ofAtom x

  shiftConstLikeReflection (distance : Nat) (innerExpr : Expr) (shiftOp : Nat → BVUnOp)
      (shiftOpName : Name) (congrThm : Name) :
      M (Option ReifiedBVExpr) := do
    let some inner ← ofOrAtom innerExpr | return none
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
      M (Option ReifiedBVExpr) := do
    -- Either the shift values are constant or we abstract the entire term as atoms
    let some distance ← getNatValue? distanceExpr | return ← ofAtom x
    shiftConstLikeReflection distance innerExpr rotateOp rotateOpName congrThm

  shiftConstReflection (β : Expr) (distanceExpr : Expr) (innerExpr : Expr) (shiftOp : Nat → BVUnOp)
      (shiftOpName : Name) (congrThm : Name) :
      M (Option ReifiedBVExpr) := do
    -- Either the shift values are constant or we abstract the entire term as atoms
    let some distance ← getNatOrBvValue? β distanceExpr | return ← ofAtom x
    shiftConstLikeReflection distance innerExpr shiftOp shiftOpName congrThm

  shiftReflection (β : Expr) (distanceExpr : Expr) (innerExpr : Expr)
      (shiftOp : {m n : Nat} → BVExpr m → BVExpr n → BVExpr m) (shiftOpName : Name)
      (congrThm : Name) :
      M (Option ReifiedBVExpr) := do
    let_expr BitVec _ ← β | return ← ofAtom x
    let some inner ← of innerExpr | return none
    let some distance ← of distanceExpr | return none
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
      M (Option ReifiedBVExpr) := do
    let some lhs ← ofOrAtom lhsExpr | return none
    let some rhs ← ofOrAtom rhsExpr | return none
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
    let lhsEval ← mkEvalExpr lhs.width lhs.expr
    let lhsProof ← lhs.evalsAtAtoms
    let rhsProof ← rhs.evalsAtAtoms
    let rhsEval ← mkEvalExpr rhs.width rhs.expr
    return mkApp6 congrThm lhsExpr rhsExpr lhsEval rhsEval lhsProof rhsProof

  unaryReflection (innerExpr : Expr) (op : BVUnOp) (congrThm : Name) :
      M (Option ReifiedBVExpr) := do
    let some inner ← ofOrAtom innerExpr | return none
    let bvExpr := .un op inner.bvExpr
    let expr := mkApp3 (mkConst ``BVExpr.un) (toExpr inner.width) (toExpr op) inner.expr
    let proof := unaryCongrProof inner innerExpr (mkConst congrThm)
    return some ⟨inner.width, bvExpr, proof, expr⟩

  unaryCongrProof (inner : ReifiedBVExpr) (innerExpr : Expr) (congrProof : Expr) : M Expr := do
    let innerEval ← mkEvalExpr inner.width inner.expr
    let innerProof ← inner.evalsAtAtoms
    return mkApp4 congrProof (toExpr inner.width) innerExpr innerEval innerProof

  goBvLit (x : Expr) : M (Option ReifiedBVExpr) := do
    let some ⟨width, bvVal⟩ ← getBitVecValue? x | return ← ofAtom x
    let bvExpr : BVExpr width := .const bvVal
    let expr := mkApp2 (mkConst ``BVExpr.const) (toExpr width) (toExpr bvVal)
    let proof := do
      let evalExpr ← mkEvalExpr width expr
      return mkBVRefl width evalExpr
    return some ⟨width, bvExpr, proof, expr⟩

end ReifiedBVExpr

end Frontend
end Lean.Elab.Tactic.BVDecide
