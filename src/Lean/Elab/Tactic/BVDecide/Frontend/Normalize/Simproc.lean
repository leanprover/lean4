/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Tactic.BVDecide.Normalize
import Std.Tactic.BVDecide.Syntax
import Lean.Elab.Tactic.Simp
import Lean.Elab.Tactic.BVDecide.Frontend.Attr

/-!
This module contains implementations of simprocs used in the `bv_normalize` simp set.
-/

namespace Lean.Elab.Tactic.BVDecide
namespace Frontend.Normalize

open Lean.Meta
open Std.Tactic.BVDecide.Normalize

builtin_simproc ↓ [bv_normalize] reduceCond (cond _ _ _) := fun e => do
  let_expr f@cond α c tb eb := e | return .continue
  let r ← Simp.simp c
  if r.expr.cleanupAnnotations.isConstOf ``Bool.true then
    let pr := mkApp (mkApp4 (mkConst ``Bool.cond_pos f.constLevels!) α c tb eb) (← r.getProof)
    return .visit { expr := tb, proof? := pr }
  else if r.expr.cleanupAnnotations.isConstOf ``Bool.false then
    let pr := mkApp (mkApp4 (mkConst ``Bool.cond_neg f.constLevels!) α c tb eb) (← r.getProof)
    return .visit { expr := eb, proof? := pr }
  else
    return .continue

builtin_simproc [bv_normalize] eqToBEq (((_ : Bool) = (_ : Bool))) := fun e => do
  let_expr Eq _ lhs rhs := e | return .continue
  match_expr rhs with
  | Bool.true => return .continue
  | _ =>
    let beqApp ← mkAppM ``BEq.beq #[lhs, rhs]
    let new := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) beqApp (mkConst ``Bool.true)
    let proof := mkApp2 (mkConst ``Bool.eq_to_beq) lhs rhs
    return .done { expr := new, proof? := some proof }

builtin_simproc [bv_normalize] andOnes ((_ : BitVec _) &&& (_ : BitVec _)) := fun e => do
  let_expr HAnd.hAnd _ _ _ _ lhs rhs := e | return .continue
  let some ⟨w, rhsValue⟩ ← getBitVecValue? rhs | return .continue
  if rhsValue == -1#w then
    let proof := mkApp2 (mkConst ``Std.Tactic.BVDecide.Normalize.BitVec.and_ones) (toExpr w) lhs
    return .visit { expr := lhs, proof? := some proof }
  else
    return .continue

builtin_simproc [bv_normalize] onesAnd ((_ : BitVec _) &&& (_ : BitVec _)) := fun e => do
  let_expr HAnd.hAnd _ _ _ _ lhs rhs := e | return .continue
  let some ⟨w, lhsValue⟩ ← getBitVecValue? lhs | return .continue
  if lhsValue == -1#w then
    let proof := mkApp2 (mkConst ``Std.Tactic.BVDecide.Normalize.BitVec.ones_and) (toExpr w) rhs
    return .visit { expr := rhs, proof? := some proof }
  else
    return .continue

builtin_simproc [bv_normalize] maxUlt (BitVec.ult (_ : BitVec _) (_ : BitVec _)) := fun e => do
  let_expr BitVec.ult _ lhs rhs := e | return .continue
  let some ⟨w, lhsValue⟩ ← getBitVecValue? lhs | return .continue
  if lhsValue == -1#w then
    let proof := mkApp2 (mkConst ``Std.Tactic.BVDecide.Normalize.BitVec.max_ult') (toExpr w) rhs
    return .visit { expr := toExpr Bool.false, proof? := some proof }
  else
    return .continue

-- A specialised version of BitVec.neg_eq_not_add so it doesn't trigger on -constant
builtin_simproc [bv_normalize] neg_eq_not_add (-(_ : BitVec _)) := fun e => do
  let_expr Neg.neg typ _ val := e | return .continue
  let_expr BitVec widthExpr := typ | return .continue
  let some w ← getNatValue? widthExpr | return .continue
  match ← getBitVecValue? val with
  | some _ => return .continue
  | none =>
    let proof := mkApp2 (mkConst ``BitVec.neg_eq_not_add) (toExpr w) val
    let expr ← mkAppM ``HAdd.hAdd #[← mkAppM ``Complement.complement #[val], (toExpr 1#w)]
    return .visit { expr := expr, proof? := some proof }

builtin_simproc [bv_normalize] bv_add_const ((_ : BitVec _) + ((_ : BitVec _) + (_ : BitVec _))) :=
  fun e => do
    let_expr HAdd.hAdd _ _ _ _ exp1 rhs := e | return .continue
    let_expr HAdd.hAdd _ _ _ _ exp2 exp3 := rhs | return .continue
    let some ⟨w, exp1Val⟩ ←  getBitVecValue? exp1 | return .continue
    let proofBuilder thm := mkApp4 (mkConst thm) (toExpr w) exp1 exp2 exp3
    match ← getBitVecValue? exp2 with
    | some ⟨w', exp2Val⟩ =>
      if h : w = w' then
        let newLhs := exp1Val + h ▸ exp2Val
        let expr ← mkAppM ``HAdd.hAdd #[toExpr newLhs, exp3]
        let proof := proofBuilder ``Std.Tactic.BVDecide.Normalize.BitVec.add_const_left
        return .visit { expr := expr, proof? := some proof }
      else
        return .continue
    | none =>
      let some ⟨w', exp3Val⟩ ← getBitVecValue? exp3 | return .continue
      if h : w = w' then
        let newLhs := exp1Val + h ▸ exp3Val
        let expr ← mkAppM ``HAdd.hAdd #[toExpr newLhs, exp2]
        let proof := proofBuilder ``Std.Tactic.BVDecide.Normalize.BitVec.add_const_right
        return .visit { expr := expr, proof? := some proof }
      else
        return .continue

builtin_simproc [bv_normalize] bv_add_const' (((_ : BitVec _) + (_ : BitVec _)) + (_ : BitVec _)) :=
  fun e => do
    let_expr HAdd.hAdd _ _ _ _ lhs exp3 := e | return .continue
    let_expr HAdd.hAdd _ _ _ _ exp1 exp2 := lhs | return .continue
    let some ⟨w, exp3Val⟩ ←  getBitVecValue? exp3 | return .continue
    let proofBuilder thm := mkApp4 (mkConst thm) (toExpr w) exp1 exp2 exp3
    match ← getBitVecValue? exp1 with
    | some ⟨w', exp1Val⟩ =>
      if h : w = w' then
        let newLhs := exp3Val + h ▸ exp1Val
        let expr ← mkAppM ``HAdd.hAdd #[toExpr newLhs, exp2]
        let proof := proofBuilder ``Std.Tactic.BVDecide.Normalize.BitVec.add_const_left'
        return .visit { expr := expr, proof? := some proof }
      else
        return .continue
    | none =>
      let some ⟨w', exp2Val⟩ ← getBitVecValue? exp2 | return .continue
      if h : w = w' then
        let newLhs := exp3Val + h ▸ exp2Val
        let expr ← mkAppM ``HAdd.hAdd #[toExpr newLhs, exp1]
        let proof := proofBuilder ``Std.Tactic.BVDecide.Normalize.BitVec.add_const_right'
        return .visit { expr := expr, proof? := some proof }
      else
        return .continue

/-- Return a number `k` such that `2^k = n`. -/
private def Nat.log2Exact (n : Nat) : Option Nat := do
  guard <| n ≠ 0
  let k := n.log2
  guard <| Nat.pow 2 k == n
  return k

-- Build an expression for `x ^ y`.
def mkPow (x y : Expr) : MetaM Expr := mkAppM ``HPow.hPow #[x, y]

builtin_simproc [bv_normalize] bv_udiv_of_two_pow (((_ : BitVec _) / (BitVec.ofNat _ _) : BitVec _)) := fun e => do
  let_expr HDiv.hDiv _α _β _γ _self x y := e | return .continue
  let some ⟨w, yVal⟩ ← getBitVecValue? y | return .continue
  let n := yVal.toNat
  -- BitVec.ofNat w n, where n =def= 2^k
  let some k := Nat.log2Exact n | return .continue
  -- check that k < w.
  if k ≥ w then return .continue
  let rhs ← mkAppM ``HShiftRight.hShiftRight #[x, mkNatLit k]
  -- 2^k = n
  let hk ← mkDecideProof (← mkEq (← mkPow (mkNatLit 2) (mkNatLit k)) (mkNatLit n))
  -- k < w
  let hlt ← mkDecideProof (← mkLt (mkNatLit k) (mkNatLit w))
  let proof := mkAppN (mkConst ``Std.Tactic.BVDecide.Normalize.BitVec.udiv_ofNat_eq_of_lt)
    #[mkNatLit w, x, mkNatLit n, mkNatLit k, hk, hlt]
  return .done {
      expr :=  rhs
      proof? := some proof
  }

builtin_simproc [bv_normalize] bv_equal_const_not (~~~(_ : BitVec _) == (_ : BitVec _)) :=
  fun e => do
    let_expr BEq.beq α inst outerLhs rhs := e | return .continue
    let some ⟨w, rhsVal⟩ ← getBitVecValue? rhs | return .continue
    let_expr Complement.complement _ _ lhs := outerLhs | return .continue
    let expr := mkApp4 (mkConst ``BEq.beq [0]) α inst lhs (toExpr (~~~rhsVal))
    let proof :=
      mkApp3 (mkConst ``Std.Tactic.BVDecide.Frontend.Normalize.BitVec.not_eq_comm)
        (toExpr w)
        lhs
        rhs
    return .visit { expr := expr, proof? := some proof }

builtin_simproc [bv_normalize] bv_equal_const_not' ((_ : BitVec _) == ~~~(_ : BitVec _)) :=
  fun e => do
    let_expr BEq.beq α inst lhs outerRhs := e | return .continue
    let some ⟨w, lhsVal⟩ ← getBitVecValue? lhs | return .continue
    let_expr Complement.complement _ _ rhs := outerRhs | return .continue
    let expr := mkApp4 (mkConst ``BEq.beq [0]) α inst rhs (toExpr (~~~lhsVal))
    let proof :=
      mkApp3 (mkConst ``Std.Tactic.BVDecide.Frontend.Normalize.BitVec.not_eq_comm')
        (toExpr w)
        lhs
        rhs
    return .visit { expr := expr, proof? := some proof }

builtin_simproc [bv_normalize] bv_and_eq_allOnes ((_ : BitVec _) &&& (_ : BitVec _) == (_ : BitVec _)) :=
  fun e => do
    let_expr BEq.beq α instBEq outerLhs rhs := e | return .continue
    let some ⟨w, rhsVal⟩ ← getBitVecValue? rhs | return .continue
    if -1#w != rhsVal then return .continue
    let_expr HAnd.hAnd _ _ _ _ llhs lrhs := outerLhs | return .continue
    let newLhs := mkApp4 (mkConst ``BEq.beq [0]) α instBEq llhs rhs
    let newRhs := mkApp4 (mkConst ``BEq.beq [0]) α instBEq lrhs rhs
    let expr := mkApp2 (mkConst ``Bool.and) newLhs newRhs
    let proof :=
      mkApp3 (mkConst ``Std.Tactic.BVDecide.Frontend.Normalize.BitVec.and_eq_allOnes)
        (toExpr w)
        llhs
        lrhs
    return .visit { expr := expr, proof? := some proof }

builtin_simproc [bv_normalize] bv_allOnes_eq_and ((_ : BitVec _) == (_ : BitVec _) &&& (_ : BitVec _)) :=
  fun e => do
    let_expr BEq.beq α instBEq lhs outerRhs := e | return .continue
    let some ⟨w, lhsVal⟩ ← getBitVecValue? lhs | return .continue
    if -1#w != lhsVal then return .continue
    let_expr HAnd.hAnd _ _ _ _ rlhs rrhs := outerRhs | return .continue
    let newLhs := mkApp4 (mkConst ``BEq.beq [0]) α instBEq rlhs lhs
    let newRhs := mkApp4 (mkConst ``BEq.beq [0]) α instBEq rrhs lhs
    let expr := mkApp2 (mkConst ``Bool.and) newLhs newRhs
    let proof :=
      mkApp3 (mkConst ``Std.Tactic.BVDecide.Frontend.Normalize.BitVec.allOnes_eq_and)
        (toExpr w)
        rlhs
        rrhs
    return .visit { expr := expr, proof? := some proof }

builtin_simproc [bv_normalize] bv_extractLsb'_not (BitVec.extractLsb' _ _ (~~~(_ : BitVec _))) :=
  fun e => do
    let_expr BitVec.extractLsb' initialWidth start len inner := e | return .continue
    let some initialWidthVal ← getNatValue? initialWidth | return .continue
    let some startVal ← getNatValue? start | return .continue
    let some lenVal ← getNatValue? len | return .continue
    if !(startVal + lenVal) < initialWidthVal then return .continue
    let_expr Complement.complement _ _ inner := inner | return .continue
    let newInner := mkApp4 (mkConst ``BitVec.extractLsb') initialWidth start len inner
    let expr ← mkAppM ``Complement.complement #[newInner]
    let lt ← mkDecideProof (← mkAppM ``LT.lt #[(← mkAppM ``HAdd.hAdd #[start, len]), initialWidth])
    let proof := mkApp5 (mkConst ``BitVec.extractLsb'_not_of_lt) initialWidth inner start len lt
    return .visit { expr := expr, proof? := some proof }

def isTwoPow (x : BitVec w) : Option Nat :=
  if x == 0#w then
    none
  else
    go x 0
where
  go {w : Nat} (x : BitVec w) (counter : Nat) : Option Nat :=
    if counter < w then
      let attempt := 1#w <<< counter
      if attempt == x then
        some counter
      else
        go x (counter + 1)
    else
      none

builtin_simproc [bv_normalize] bv_twoPow_mul ((BitVec.ofNat _ _) * (_ : BitVec _)) :=
  fun e => do
    let_expr HMul.hMul _ _ _ _ lhsExpr rhs := e | return .continue
    let some ⟨w, lhs⟩ ← getBitVecValue? lhsExpr | return .continue
    let some pow := isTwoPow lhs | return .continue
    let expr ← mkAppM ``HShiftLeft.hShiftLeft #[rhs, toExpr pow]
    let proof := mkApp3 (mkConst ``BitVec.twoPow_mul_eq_shiftLeft) (toExpr w) rhs (toExpr pow)
    return .visit { expr := expr, proof? := some proof }

builtin_simproc [bv_normalize] bv_mul_twoPow ((_ : BitVec _) * (BitVec.ofNat _ _)) :=
  fun e => do
    let_expr HMul.hMul _ _ _ _ lhs rhsExpr := e | return .continue
    let some ⟨w, rhs⟩ ← getBitVecValue? rhsExpr | return .continue
    let some pow := isTwoPow rhs | return .continue
    let expr ← mkAppM ``HShiftLeft.hShiftLeft #[lhs, toExpr pow]
    let proof := mkApp3 (mkConst ``BitVec.mul_twoPow_eq_shiftLeft) (toExpr w) lhs (toExpr pow)
    return .visit { expr := expr, proof? := some proof }

end Frontend.Normalize
end Lean.Elab.Tactic.BVDecide
