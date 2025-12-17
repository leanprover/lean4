/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Tactic.BVDecide.Normalize
public import Lean.Elab.Tactic.BVDecide.Frontend.Attr

public section

/-!
This module contains implementations of simprocs used in the `bv_normalize` simp set.
-/

namespace Lean.Elab.Tactic.BVDecide
namespace Frontend.Normalize

open Lean.Meta
open Std.Tactic.BVDecide.Normalize

private def mkDecideProofWith (p : Expr) (inst : Expr) : Expr :=
  let decP := mkApp2 (mkConst ``Decidable.decide) p inst
  let boolTy := mkConst ``Bool
  let decEqTrue := mkApp3 (mkConst ``Eq [1]) boolTy decP (mkConst ``Bool.true)
  let h := mkApp2 (mkConst ``Eq.refl [1]) boolTy (mkConst ``Bool.true)
  let h := mkExpectedPropHint h decEqTrue
  mkApp3 (mkConst ``of_decide_eq_true) p inst h

namespace BitVec

private def mkComplement (e : Expr) (wExpr : Expr) : Expr :=
  let ty := mkApp (mkConst ``BitVec) wExpr
  let inst := mkApp (mkConst ``BitVec.instComplement) wExpr
  mkApp3 (mkConst ``Complement.complement [0]) ty inst e

private def mkNeg (e : Expr) (wExpr : Expr) : Expr :=
  let ty := mkApp (mkConst ``BitVec) wExpr
  let inst := mkApp (mkConst ``BitVec.instNeg) wExpr
  mkApp3 (mkConst ``Neg.neg [0]) ty inst e

private def mkOr (lhs rhs : Expr) (wExpr : Expr) : Expr :=
  let ty := mkApp (mkConst ``BitVec) wExpr
  let inst := mkApp2 (mkConst ``instHOrOfOrOp [0]) ty (mkApp (mkConst ``BitVec.instOrOp) wExpr)
  mkApp6 (mkConst ``HOr.hOr [0, 0, 0]) ty ty ty inst lhs rhs

private def mkAnd (lhs rhs : Expr) (wExpr : Expr) : Expr :=
  let ty := mkApp (mkConst ``BitVec) wExpr
  let inst := mkApp2 (mkConst ``instHAndOfAndOp [0]) ty (mkApp (mkConst ``BitVec.instAndOp) wExpr)
  mkApp6 (mkConst ``HAnd.hAnd [0, 0, 0]) ty ty ty inst lhs rhs

private def mkXor (lhs rhs : Expr) (wExpr : Expr) : Expr :=
  let ty := mkApp (mkConst ``BitVec) wExpr
  let inst := mkApp2 (mkConst ``instHXorOfXorOp [0]) ty (mkApp (mkConst ``BitVec.instXorOp) wExpr)
  mkApp6 (mkConst ``HXor.hXor [0, 0, 0]) ty ty ty inst lhs rhs

private def mkAdd (lhs rhs : Expr) (wExpr : Expr) : Expr :=
  let ty := mkApp (mkConst ``BitVec) wExpr
  let inst := mkApp2 (mkConst ``instHAdd [0]) ty (mkApp (mkConst ``BitVec.instAdd) wExpr)
  mkApp6 (mkConst ``HAdd.hAdd [0, 0, 0]) ty ty ty inst lhs rhs

private def mkMul (lhs rhs : Expr) (wExpr : Expr) : Expr :=
  let ty := mkApp (mkConst ``BitVec) wExpr
  let inst := mkApp2 (mkConst ``instHMul [0]) ty (mkApp (mkConst ``BitVec.instMul) wExpr)
  mkApp6 (mkConst ``HMul.hMul [0, 0, 0]) ty ty ty inst lhs rhs

private def mkAppend (lhs rhs : Expr) (wlExpr wrExpr wResExpr : Expr) : Expr :=
  let lty := mkApp (mkConst ``BitVec) wlExpr
  let rty := mkApp (mkConst ``BitVec) wrExpr
  let resty := mkApp (mkConst ``BitVec) wResExpr
  let inst := mkApp2 (mkConst ``BitVec.instHAppendHAddNat) wlExpr wrExpr
  mkApp6 (mkConst ``HAppend.hAppend [0, 0, 0]) lty rty resty inst lhs rhs

private def mkNatShiftRight (lhs rhs : Expr) (wExpr : Expr) : Expr :=
  let ty := mkApp (mkConst ``BitVec) wExpr
  let inst := mkApp (mkConst ``BitVec.instHShiftRightNat) wExpr
  mkApp6 (mkConst ``HShiftRight.hShiftRight [0, 0, 0]) ty (mkConst ``Nat) ty inst lhs rhs

private def mkNatShiftLeft (lhs rhs : Expr) (wExpr : Expr) : Expr :=
  let ty := mkApp (mkConst ``BitVec) wExpr
  let inst := mkApp (mkConst ``BitVec.instHShiftLeftNat) wExpr
  mkApp6 (mkConst ``HShiftLeft.hShiftLeft [0, 0, 0]) ty (mkConst ``Nat) ty inst lhs rhs

private def mkBEq (lhs rhs : Expr) (wExpr : Expr) : Expr :=
  let ty := mkApp (mkConst ``BitVec) wExpr
  let instDec := mkApp (mkConst ``instDecidableEqBitVec) wExpr
  let inst := mkApp2 (mkConst ``instBEqOfDecidableEq [0]) ty instDec
  mkApp4 (mkConst ``BEq.beq [0]) ty inst lhs rhs

end BitVec

namespace Nat

private def mkDecideProofEq (lhs rhs : Expr) : Expr :=
  let p := mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) lhs rhs
  let inst := mkApp2 (mkConst ``instDecidableEqNat) lhs rhs
  mkDecideProofWith p inst

private def mkDecideProofLt (lhs rhs : Expr) : Expr :=
  let p := mkApp4 (mkConst ``LT.lt [0]) (mkConst ``Nat) (mkConst ``instLTNat) lhs rhs
  let inst := mkApp2 (mkConst ``Nat.decLt) lhs rhs
  mkDecideProofWith p inst

private def mkDecideProofLe (lhs rhs : Expr) : Expr :=
  let p := mkApp4 (mkConst ``LE.le [0]) (mkConst ``Nat) (mkConst ``instLENat) lhs rhs
  let inst := mkApp2 (mkConst ``Nat.decLe) lhs rhs
  mkDecideProofWith p inst

private def mkPow (lhs rhs : Expr) : Expr :=
  let ty := mkConst ``Nat
  let instPow := mkApp2 (mkConst ``instPowNat [0]) ty (mkConst ``instNatPowNat)
  let inst := mkApp3 (mkConst ``instHPow [0, 0]) ty ty instPow
  mkApp6 (mkConst ``HPow.hPow [0, 0, 0]) ty ty ty inst lhs rhs

private def mkAdd (lhs rhs : Expr) : Expr :=
  let ty := mkConst ``Nat
  let inst := mkApp2 (mkConst ``instHAdd [0]) ty (mkConst ``instAddNat)
  mkApp6 (mkConst ``HAdd.hAdd [0, 0, 0]) ty ty ty inst lhs rhs

end Nat

section SimpleUnifiers

builtin_simproc [bv_normalize] bv_and ((_ : BitVec _) &&& (_ : BitVec _)) := fun e => do
  let_expr HAnd.hAnd ty _ _ _ lhs rhs := e | return .continue
  let_expr BitVec wExpr := ty | return .continue
  if lhs == rhs then
    return .visit { expr := lhs, proof? := some <| mkApp2 (mkConst ``BitVec.and_self) wExpr lhs }
  else
    let some w ← getNatValue? wExpr | return .continue
    let tryIt (notSide other : Expr) : Bool :=
      let_expr Complement.complement _ _ notSide := notSide | false
      notSide == other

    if tryIt lhs rhs then
      let proof := mkApp2 (mkConst ``BitVec.and_contra') wExpr rhs
      return .visit { expr := toExpr 0#w, proof? := some proof }
    else if tryIt rhs lhs then
      let proof := mkApp2 (mkConst ``BitVec.and_contra) wExpr lhs
      return .visit { expr := toExpr 0#w, proof? := some proof }
    else
      return .continue

builtin_simproc [bv_normalize] bv_add ((_ : BitVec _) + (_ : BitVec _)) := fun e => do
  let_expr HAdd.hAdd ty _ _ _ lhs rhs := e | return .continue
  let_expr BitVec wExpr := ty | return .continue
  let some w ← getNatValue? wExpr | return .continue
  if lhs == rhs then
    let expr ← mkMul lhs (toExpr 2#w)
    return .visit { expr , proof? := some <| mkApp2 (mkConst ``BitVec.add_same) wExpr lhs }
  else
    let notAdd : MetaM (Option Simp.Step) := do
      let_expr Complement.complement _ _ lhs := lhs | return none
      if lhs != rhs then return none
      let proof := mkApp2 (mkConst ``BitVec.not_add) wExpr rhs
      return some <| .visit { expr := toExpr (-1#w) , proof? := some proof }

    let addNot : MetaM (Option Simp.Step) := do
      let_expr Complement.complement _ _ rhs := rhs | return none
      if lhs != rhs then return none
      let proof := mkApp2 (mkConst ``BitVec.add_not) wExpr lhs
      return some <| .visit { expr := toExpr (-1#w) , proof? := some proof }

    let addNeg : MetaM (Option Simp.Step) := do
      let_expr HAdd.hAdd _ _ _ _ rlhs rrhs := rhs | return none
      let some ⟨w', rrhsVal⟩ ← getBitVecValue? rrhs | return none
      if rrhsVal != 1#w' then return none
      let_expr Complement.complement _ _ rlhs := rlhs | return none
      if rlhs != lhs then return none
      let proof := mkApp2 (mkConst ``BitVec.add_neg) wExpr lhs
      return some <| .visit { expr := toExpr 0#w, proof? := some proof }

    let negAdd : MetaM (Option Simp.Step) := do
      let_expr HAdd.hAdd _ _ _ _ llhs lrhs := lhs | return none
      let some ⟨w', lrhsVal⟩ ← getBitVecValue? lrhs | return none
      if lrhsVal != 1#w' then return none
      let_expr Complement.complement _ _ llhs := llhs | return none
      if llhs != rhs then return none
      let proof := mkApp2 (mkConst ``Std.Tactic.BVDecide.Normalize.BitVec.neg_add) wExpr rhs
      return some <| .visit { expr := toExpr 0#w, proof? := some proof }

    let addNegMul : MetaM (Option Simp.Step) := do
      let some ⟨w', rhsVal⟩ ← getBitVecValue? rhs | return none
      if rhsVal != 1#w' then return none
      let_expr Complement.complement _ _ lhs := lhs | return none
      let_expr HAdd.hAdd _ _ _ _ llhs lrhs := lhs | return none
      if llhs.isAppOf ``HMul.hMul then
        let_expr HMul.hMul _ _ _ _ lllhs llrhs := llhs | return none
        if lllhs == lrhs then
          let newRhs := BitVec.mkComplement llrhs wExpr
          let expr := BitVec.mkMul lllhs newRhs wExpr
          let proof := mkApp3 (mkConst ``BitVec.add_neg_mul'') wExpr lllhs llrhs
          return some <| .visit { expr := expr, proof? := some proof }
        else if llrhs == lrhs then
          let newLhs := BitVec.mkComplement lllhs wExpr
          let expr := BitVec.mkMul newLhs llrhs wExpr
          let proof := mkApp3 (mkConst ``BitVec.add_neg_mul''') wExpr llrhs lllhs
          return some <| .visit { expr := expr, proof? := some proof }
        else
          return none
      else if lrhs.isAppOf ``HMul.hMul then
        let_expr HMul.hMul _ _ _ _ lrlhs lrrhs := lrhs | return none
        if llhs == lrlhs then
          let newRhs := BitVec.mkComplement lrrhs wExpr
          let expr := BitVec.mkMul lrlhs newRhs wExpr
          let proof := mkApp3 (mkConst ``BitVec.add_neg_mul) wExpr lrlhs lrrhs
          return some <| .visit { expr := expr, proof? := some proof }
        else if llhs == lrrhs then
          let newLhs := BitVec.mkComplement lrlhs wExpr
          let expr := BitVec.mkMul newLhs lrrhs wExpr
          let proof := mkApp3 (mkConst ``BitVec.add_neg_mul') wExpr lrrhs lrlhs
          return some <| .visit { expr := expr, proof? := some proof }
        else
          return none
      else
        return none

    let addShiftLeft : MetaM (Option Simp.Step) := do
      let_expr HShiftLeft.hShiftLeft _ _ _ _ rlhs rrhs := rhs | return none
      if lhs != rrhs then return none
      let expr := BitVec.mkOr lhs rhs wExpr
      let proof := mkApp3 (mkConst ``BitVec.add_shiftLeft_eq_or_shiftLeft) wExpr lhs rlhs
      return some <| .visit { expr := expr, proof? := some proof }

    let shiftLeftAdd : MetaM (Option Simp.Step) := do
      let_expr HShiftLeft.hShiftLeft _ _ _ _ llhs lrhs := lhs | return none
      if rhs != lrhs then return none
      let expr := BitVec.mkOr lhs rhs wExpr
      let proof := mkApp3 (mkConst ``BitVec.shiftLeft_add_eq_shiftLeft_or) wExpr rhs llhs
      return some <| .visit { expr := expr, proof? := some proof }

    if let some step ← notAdd then return step
    else if let some step ← addNot then return step
    else if let some step ← addNeg then return step
    else if let some step ← negAdd then return step
    else if let some step ← addNegMul then return step
    else if let some step ← addShiftLeft then return step
    else if let some step ← shiftLeftAdd then return step
    else return .continue

builtin_simproc [bv_normalize] shiftRight ((_ : BitVec _) >>> (_ : BitVec _)) := fun e => do
  let_expr HShiftRight.hShiftRight ty _ _ _ lhs rhs := e | return .continue
  let_expr BitVec wExpr := ty | return .continue
  let some w ← getNatValue? wExpr | return .continue
  if lhs == rhs then
    let proof := mkApp2 (mkConst ``Std.Tactic.BVDecide.Normalize.BitVec.ushiftRight_self) wExpr lhs
    return .visit { expr := toExpr 0#w, proof? := some proof }
  else
    let_expr BitVec.ofNat nExpr kExpr := rhs | return .continue
    let some n ← getNatValue? nExpr | return .continue
    if w != n then return .continue
    let some k ← getNatValue? kExpr | return .continue
    let expr := BitVec.mkNatShiftRight lhs (toExpr (k % 2 ^ w)) wExpr
    let proof := mkApp3 (mkConst ``BitVec.ushiftRight_ofNat_eq) wExpr lhs kExpr
    return .visit { expr, proof? := some proof }

builtin_simproc [bv_normalize] extractLsb' (BitVec.extractLsb' _ _ _) := fun e => do
  let_expr BitVec.extractLsb' wExpr startExpr lenExpr targetExpr := e | return .continue
  match_expr targetExpr with
  | HAnd.hAnd _ _ _ _ lhs rhs =>
    let lhs' := mkApp4 (mkConst ``BitVec.extractLsb') wExpr startExpr lenExpr lhs
    let rhs' := mkApp4 (mkConst ``BitVec.extractLsb') wExpr startExpr lenExpr rhs
    let expr := BitVec.mkAnd lhs' rhs' lenExpr
    let proof := mkApp5 (mkConst ``BitVec.extractLsb'_and) wExpr lhs rhs startExpr lenExpr
    return .visit { expr, proof? := some proof }
  | HXor.hXor _ _ _ _ lhs rhs =>
    let lhs' := mkApp4 (mkConst ``BitVec.extractLsb') wExpr startExpr lenExpr lhs
    let rhs' := mkApp4 (mkConst ``BitVec.extractLsb') wExpr startExpr lenExpr rhs
    let expr := BitVec.mkXor lhs' rhs' lenExpr
    let proof := mkApp5 (mkConst ``BitVec.extractLsb'_xor) wExpr lhs rhs startExpr lenExpr
    return .visit { expr, proof? := some proof }
  | cond _ discr thenExpr elseExpr =>
    let thenExpr' := mkApp4 (mkConst ``BitVec.extractLsb') wExpr startExpr lenExpr thenExpr
    let elseExpr' := mkApp4 (mkConst ``BitVec.extractLsb') wExpr startExpr lenExpr elseExpr
    let newTy := mkApp (mkConst ``BitVec) lenExpr
    let expr := mkApp4 (mkConst ``cond [1]) newTy discr thenExpr' elseExpr'
    let proof :=
      mkApp6 (mkConst ``Std.Tactic.BVDecide.Normalize.BitVec.extractLsb'_if)
        wExpr
        discr
        thenExpr
        elseExpr
        startExpr
        lenExpr
     return .visit { expr, proof? := some proof }
  | _ =>
    let some w ← getNatValue? wExpr | return .continue
    let some start ← getNatValue? startExpr | return .continue
    let some len ← getNatValue? lenExpr | return .continue
    if start != 0 then return .continue
    if len != w then return .continue
    let proof := mkApp2 (mkConst ``BitVec.extractLsb'_eq_self) wExpr targetExpr
    return .visit { expr := targetExpr, proof? := some proof }

builtin_simproc [bv_normalize] shiftLeft ((_ : BitVec _) <<< (_ : BitVec _)) := fun e => do
  let_expr HShiftLeft.hShiftLeft ty _ _ _ lhs rhs := e | return .continue
  let_expr BitVec wExpr := ty | return .continue
  let some w ← getNatValue? wExpr | return .continue
  let_expr BitVec.ofNat nExpr kExpr := rhs | return .continue
  let some n ← getNatValue? nExpr | return .continue
  if w != n then return .continue
  let some k ← getNatValue? kExpr | return .continue
  let expr := BitVec.mkNatShiftLeft lhs (toExpr (k % 2 ^ w)) wExpr
  let proof := mkApp3 (mkConst ``BitVec.shiftLeft_ofNat_eq) wExpr lhs kExpr
  return .visit { expr, proof? := some proof }

builtin_simproc [bv_normalize] sshiftRight' (BitVec.sshiftRight' _ _) := fun e => do
  let_expr BitVec.sshiftRight' nExpr mExpr lhs rhs := e | return .continue
  let some n ← getNatValue? nExpr | return .continue
  let some m ← getNatValue? mExpr | return .continue
  if n != m then return .continue
  let_expr BitVec.ofNat wExpr kExpr := rhs | return .continue
  let some w ← getNatValue? wExpr | return .continue
  if n != w then return .continue
  let some k ← getNatValue? kExpr | return .continue
  let expr := mkApp3 (mkConst ``BitVec.sshiftRight) wExpr lhs (toExpr (k % 2 ^ w))
  let proof := mkApp3 (mkConst ``BitVec.sshiftRight'_ofNat_eq_sshiftRight) wExpr lhs kExpr
  return .visit { expr, proof? := some proof }

def eqSelfProc : Simp.Simproc := fun e => do
  let_expr Eq ty lhs rhs := e | return .continue
  if lhs != rhs then return .continue
  let proof := mkApp2 (mkConst ``eq_self [1]) ty lhs
  return .visit { expr := mkConst ``True, proof? := some proof }

builtin_simproc [bv_normalize] bv_eq_self ((_ : BitVec _) = (_ : BitVec _)) := eqSelfProc
builtin_simproc [bv_normalize] bool_eq_self ((_ : Bool) = (_ : Bool)) := eqSelfProc

builtin_simproc [bv_normalize] bool_and ((_ : Bool) && (_ : Bool)) := fun e => do
  let_expr Bool.and lhs rhs := e | return .continue
  if lhs == rhs then
    return .visit { expr := lhs, proof? := some (mkApp (mkConst ``Bool.and_self) lhs) }
  else
    let andNotSelf : MetaM (Option Simp.Step) := do
      let_expr Bool.not rhs := rhs | return none
      if lhs != rhs then return none
      let proof := mkApp (mkConst ``Bool.and_not_self) lhs
      return some <| .visit { expr := toExpr false, proof? := some proof }

    let notAndSelf : MetaM (Option Simp.Step) := do
      let_expr Bool.not lhs := lhs | return none
      if lhs != rhs then return none
      let proof := mkApp (mkConst ``Bool.not_and_self) lhs
      return some <| .visit { expr := toExpr false, proof? := some proof }

    let andSelfLeft : MetaM (Option Simp.Step) := do
      let_expr Bool.and rlhs rrhs := rhs | return none
      if lhs != rlhs then return none
      let expr := mkApp2 (mkConst ``Bool.and) lhs rrhs
      let proof := mkApp2 (mkConst ``Bool.and_self_left) lhs rrhs
      return some <| .visit { expr := expr, proof? := some proof }

    let andSelfRight : MetaM (Option Simp.Step) := do
      let_expr Bool.and llhs lrhs := lhs | return none
      if rhs != lrhs then return none
      let expr := mkApp2 (mkConst ``Bool.and) llhs rhs
      let proof := mkApp2 (mkConst ``Bool.and_self_right) llhs rhs
      return some <| .visit { expr := expr, proof? := some proof }

    if let some step ← andNotSelf then return step
    else if let some step ← notAndSelf then return step
    else if let some step ← andSelfLeft then return step
    else if let some step ← andSelfRight then return step
    else return .continue

builtin_simproc [bv_normalize] bv_beq_self ((_ : BitVec _) == (_ : BitVec _)) := fun e => do
  let_expr BEq.beq ty _ lhs rhs := e | return .continue
  let_expr BitVec wExpr := ty | return .continue
  if lhs != rhs then return .continue
  let proof :=
    mkApp2
      (mkConst ``Std.Tactic.BVDecide.Normalize.BitVec.beq_self_eq_true)
      wExpr
      lhs
  return .visit { expr := toExpr true, proof? := some proof }

builtin_simproc [bv_normalize] bool_beq ((_ : Bool) == (_ : Bool)) := fun e => do
  let_expr BEq.beq _ _ lhs rhs := e | return .continue
  if lhs == rhs then
  let proof := mkApp (mkConst ``Std.Tactic.BVDecide.Normalize.Bool.beq_self_eq_true) lhs
    return .visit { expr := toExpr true, proof? := some proof }
  else
    let notSelf : MetaM (Option Simp.Step) := do
      let_expr Bool.not rhs := rhs | return none
      if lhs != rhs then return none
      let proof := mkApp (mkConst ``Bool.beq_not_self) lhs
      return some <| .visit { expr := toExpr false, proof? := some proof }

    let selfNot : MetaM (Option Simp.Step) := do
      let_expr Bool.not lhs := lhs | return none
      if lhs != rhs then return none
      let proof := mkApp (mkConst ``Bool.not_beq_self) lhs
      return some <| .visit { expr := toExpr false, proof? := some proof }

    let selfLeft : MetaM (Option Simp.Step) := do
      let_expr BEq.beq _ _ rlhs rrhs := rhs | return none
      if lhs != rlhs then return none
      let proof := mkApp2 (mkConst ``Bool.beq_self_left) lhs rrhs
      return some <| .visit { expr := rrhs, proof? := some proof }

    let selfRight : MetaM (Option Simp.Step) := do
      let_expr BEq.beq _ _ llhs lrhs := lhs | return none
      if rhs != lrhs then return none
      let proof := mkApp2 (mkConst ``Bool.beq_self_right) llhs rhs
      return some <| .visit { expr := llhs, proof? := some proof }

    if let some step ← notSelf then return step
    else if let some step ← selfNot then return step
    else if let some step ← selfLeft then return step
    else if let some step ← selfRight then return step
    else return .continue

builtin_simproc [bv_normalize] cast (BitVec.cast _ _) := fun e => do
  let_expr BitVec.cast nExpr mExpr hExpr targetExpr := e | return .continue
  let some n ← getNatValue? nExpr | return .continue
  let some m ← getNatValue? mExpr | return .continue
  if n != m then return .continue
  let proof := mkApp3 (mkConst ``BitVec.cast_eq) nExpr hExpr targetExpr
  return .visit { expr := targetExpr, proof? := some proof }

end SimpleUnifiers

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

builtin_simproc [bv_normalize] andOnes ((_ : BitVec _) &&& (BitVec.ofNat _ _)) := fun e => do
  let_expr HAnd.hAnd _ _ _ _ lhs rhs := e | return .continue
  let some ⟨w, rhsValue⟩ ← getBitVecValue? rhs | return .continue
  if rhsValue == -1#w then
    let proof := mkApp2 (mkConst ``Std.Tactic.BVDecide.Normalize.BitVec.and_ones) (toExpr w) lhs
    return .visit { expr := lhs, proof? := some proof }
  else
    return .continue

builtin_simproc [bv_normalize] onesAnd ((BitVec.ofNat _ _) &&& (_ : BitVec _)) := fun e => do
  let_expr HAnd.hAnd _ _ _ _ lhs rhs := e | return .continue
  let some ⟨w, lhsValue⟩ ← getBitVecValue? lhs | return .continue
  if lhsValue == -1#w then
    let proof := mkApp2 (mkConst ``Std.Tactic.BVDecide.Normalize.BitVec.ones_and) (toExpr w) rhs
    return .visit { expr := rhs, proof? := some proof }
  else
    return .continue

builtin_simproc [bv_normalize] maxUlt (BitVec.ult (BitVec.ofNat _ _) (_ : BitVec _)) := fun e => do
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
  let_expr BitVec wExpr := typ | return .continue
  let some w ← getNatValue? wExpr | return .continue
  match ← getBitVecValue? val with
  | some _ => return .continue
  | none =>
    let proof := mkApp2 (mkConst ``BitVec.neg_eq_not_add) (toExpr w) val
    let expr := BitVec.mkAdd (BitVec.mkComplement val wExpr) (toExpr 1#w) wExpr
    return .visit { expr := expr, proof? := some proof }

/-- Return a number `k` such that `2^k = n`. -/
private def Nat.log2Exact (n : Nat) : Option Nat := do
  guard <| n ≠ 0
  let k := n.log2
  guard <| Nat.pow 2 k == n
  return k

builtin_simproc [bv_normalize] bv_udiv_of_two_pow (((_ : BitVec _) / (BitVec.ofNat _ _) : BitVec _)) := fun e => do
  let_expr HDiv.hDiv _α _β _γ _self x y := e | return .continue
  let some ⟨w, yVal⟩ ← getBitVecValue? y | return .continue
  let n := yVal.toNat
  -- BitVec.ofNat w n, where n =def= 2^k
  let some k := Nat.log2Exact n | return .continue
  -- check that k < w.
  if k ≥ w then return .continue
  let rhs := BitVec.mkNatShiftRight x (mkNatLit k) (toExpr w)
  -- 2^k = n
  let hk := Nat.mkDecideProofEq (Nat.mkPow (mkNatLit 2) (mkNatLit k)) (mkNatLit n)
  -- k < w
  let hlt := Nat.mkDecideProofLt (mkNatLit k) (mkNatLit w)
  let proof := mkApp6 (mkConst ``Std.Tactic.BVDecide.Normalize.BitVec.udiv_ofNat_eq_of_lt)
    (toExpr w) x (toExpr n) (toExpr k) hk hlt
  return .done {
      expr :=  rhs
      proof? := some proof
  }

builtin_simproc [bv_normalize] bv_equal_const_not (~~~(_ : BitVec _) == (BitVec.ofNat _ _)) := fun e => do
  let_expr BEq.beq _ _ outerLhs rhs := e | return .continue
  let some ⟨w, rhsVal⟩ ← getBitVecValue? rhs | return .continue
  let_expr Complement.complement _ _ lhs := outerLhs | return .continue
  let expr := BitVec.mkBEq lhs (toExpr (~~~rhsVal)) (toExpr w)
  let proof :=
    mkApp3 (mkConst ``Std.Tactic.BVDecide.Frontend.Normalize.BitVec.not_eq_comm)
      (toExpr w)
      lhs
      rhs
  return .visit { expr := expr, proof? := some proof }

builtin_simproc [bv_normalize] bv_equal_const_not' ((BitVec.ofNat _ _) == ~~~(_ : BitVec _)) := fun e => do
  let_expr BEq.beq _ _ lhs outerRhs := e | return .continue
  let some ⟨w, lhsVal⟩ ← getBitVecValue? lhs | return .continue
  let_expr Complement.complement _ _ rhs := outerRhs | return .continue
  let expr := BitVec.mkBEq rhs (toExpr (~~~lhsVal)) (toExpr w)
  let proof :=
    mkApp3 (mkConst ``Std.Tactic.BVDecide.Frontend.Normalize.BitVec.not_eq_comm')
      (toExpr w)
      lhs
      rhs
  return .visit { expr := expr, proof? := some proof }

builtin_simproc [bv_normalize] bv_and_eq_allOnes ((_ : BitVec _) &&& (_ : BitVec _) == (BitVec.ofNat _ _)) := fun e => do
  let_expr BEq.beq _ _ outerLhs rhs := e | return .continue
  let some ⟨w, rhsVal⟩ ← getBitVecValue? rhs | return .continue
  if -1#w != rhsVal then return .continue
  let_expr HAnd.hAnd _ _ _ _ llhs lrhs := outerLhs | return .continue
  let newLhs := BitVec.mkBEq llhs rhs (toExpr w)
  let newRhs := BitVec.mkBEq lrhs rhs (toExpr w)
  let expr := mkApp2 (mkConst ``Bool.and) newLhs newRhs
  let proof :=
    mkApp3 (mkConst ``Std.Tactic.BVDecide.Frontend.Normalize.BitVec.and_eq_allOnes)
      (toExpr w)
      llhs
      lrhs
  return .visit { expr := expr, proof? := some proof }

builtin_simproc [bv_normalize] bv_allOnes_eq_and ((BitVec.ofNat _ _) == (_ : BitVec _) &&& (_ : BitVec _)) := fun e => do
  let_expr BEq.beq _ _ lhs outerRhs := e | return .continue
  let some ⟨w, lhsVal⟩ ← getBitVecValue? lhs | return .continue
  if -1#w != lhsVal then return .continue
  let_expr HAnd.hAnd _ _ _ _ rlhs rrhs := outerRhs | return .continue
  let newLhs := BitVec.mkBEq rlhs lhs (toExpr w)
  let newRhs := BitVec.mkBEq rrhs lhs (toExpr w)
  let expr := mkApp2 (mkConst ``Bool.and) newLhs newRhs
  let proof :=
    mkApp3 (mkConst ``Std.Tactic.BVDecide.Frontend.Normalize.BitVec.allOnes_eq_and)
      (toExpr w)
      rlhs
      rrhs
  return .visit { expr := expr, proof? := some proof }

builtin_simproc [bv_normalize] bv_extractLsb'_not (BitVec.extractLsb' _ _ (~~~(_ : BitVec _))) := fun e => do
  let_expr BitVec.extractLsb' initialWidth start len inner := e | return .continue
  let some initialWidthVal ← getNatValue? initialWidth | return .continue
  let some startVal ← getNatValue? start | return .continue
  let some lenVal ← getNatValue? len | return .continue
  if !(startVal + lenVal) < initialWidthVal then return .continue
  let_expr Complement.complement _ _ inner := inner | return .continue
  let newInner := mkApp4 (mkConst ``BitVec.extractLsb') initialWidth start len inner
  let expr := BitVec.mkComplement newInner len
  let lt := Nat.mkDecideProofLt (Nat.mkAdd start len) initialWidth
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

builtin_simproc [bv_normalize] bv_twoPow_mul ((BitVec.ofNat _ _) * (_ : BitVec _)) := fun e => do
  let_expr HMul.hMul _ _ _ _ lhsExpr rhs := e | return .continue
  let some ⟨w, lhs⟩ ← getBitVecValue? lhsExpr | return .continue
  let some pow := isTwoPow lhs | return .continue
  let expr := BitVec.mkNatShiftLeft rhs (toExpr pow) (toExpr w)
  let proof := mkApp3 (mkConst ``BitVec.twoPow_mul_eq_shiftLeft) (toExpr w) rhs (toExpr pow)
  return .visit { expr := expr, proof? := some proof }

builtin_simproc [bv_normalize] bv_mul_twoPow ((_ : BitVec _) * (BitVec.ofNat _ _)) := fun e => do
  let_expr HMul.hMul _ _ _ _ lhs rhsExpr := e | return .continue
  let some ⟨w, rhs⟩ ← getBitVecValue? rhsExpr | return .continue
  let some pow := isTwoPow rhs | return .continue
  let expr := BitVec.mkNatShiftLeft lhs (toExpr pow) (toExpr w)
  let proof := mkApp3 (mkConst ``BitVec.mul_twoPow_eq_shiftLeft) (toExpr w) lhs (toExpr pow)
  return .visit { expr := expr, proof? := some proof }

builtin_simproc [bv_normalize] bv_ones_mul ((BitVec.ofNat _ _) * (_ : BitVec _)) := fun e => do
  let_expr HMul.hMul _ _ _ _ lhsExpr rhs := e | return .continue
  let some ⟨w, lhs⟩ ← getBitVecValue? lhsExpr | return .continue
  if -1#w != lhs then return .continue
  let expr := BitVec.mkNeg rhs (toExpr w)
  let proof := mkApp2 (mkConst ``BitVec.ones_mul) (toExpr w) rhs
  return .visit { expr := expr, proof? := some proof }

builtin_simproc [bv_normalize] bv_mul_ones ((_ : BitVec _) * (BitVec.ofNat _ _)) := fun e => do
  let_expr HMul.hMul _ _ _ _ lhs rhsExpr := e | return .continue
  let some ⟨w, rhs⟩ ← getBitVecValue? rhsExpr | return .continue
  if -1#w != rhs then return .continue
  let expr := BitVec.mkNeg lhs (toExpr w)
  let proof := mkApp2 (mkConst ``BitVec.mul_ones) (toExpr w) lhs
  return .visit { expr := expr, proof? := some proof }

builtin_simproc [bv_normalize] bv_elim_ushiftRight_const ((_ : BitVec _) >>> (_ : Nat)) := fun e => do
  let_expr HShiftRight.hShiftRight bvType _ _ _ lhsExpr rhsExpr := e | return .continue
  let some rhs ← getNatValue? rhsExpr | return .continue
  let_expr BitVec wExpr := bvType | return .continue
  let some w ← getNatValue? wExpr | return .continue
  if rhs < w then
    let zero := toExpr 0#rhs
    let newLen := w - rhs
    let newLenExpr := toExpr newLen
    let extract := mkApp4 (mkConst ``BitVec.extractLsb') wExpr rhsExpr newLenExpr lhsExpr
    let concat := BitVec.mkAppend zero extract (toExpr rhs) newLenExpr (toExpr (newLen + rhs))
    let expr := mkApp4 (mkConst ``BitVec.cast) wExpr wExpr (← mkEqRefl wExpr) concat
    let h := Nat.mkDecideProofLt rhsExpr wExpr
    let proof := mkApp4 (mkConst ``BitVec.ushiftRight_eq_extractLsb'_of_lt) wExpr lhsExpr rhsExpr h
    return .done { expr := expr, proof? := some proof }
  else
    let expr := toExpr 0#w
    let h := Nat.mkDecideProofLe wExpr rhsExpr
    let proof := mkApp4 (mkConst ``BitVec.ushiftRight_eq_zero) wExpr lhsExpr rhsExpr h
    return .done { expr := expr, proof? := some proof }

builtin_simproc [bv_normalize] bv_elim_shiftLeft_const ((_ : BitVec _) <<< (_ : Nat)) := fun e => do
  let_expr HShiftLeft.hShiftLeft bvType _ _ _ lhsExpr rhsExpr := e | return .continue
  let some rhs ← getNatValue? rhsExpr | return .continue
  let_expr BitVec wExpr := bvType | return .continue
  let some w ← getNatValue? wExpr | return .continue
  if rhs < w then
    let zero := toExpr 0#rhs
    let newLen := w - rhs
    let newLenExpr := toExpr newLen
    let extract := mkApp4 (mkConst ``BitVec.extractLsb') wExpr (toExpr 0) newLenExpr lhsExpr
    let concat := BitVec.mkAppend extract zero newLenExpr (toExpr rhs) (toExpr (newLen + rhs))
    let expr := mkApp4 (mkConst ``BitVec.cast) wExpr wExpr (← mkEqRefl wExpr) concat
    let h := Nat.mkDecideProofLt rhsExpr wExpr
    let proof := mkApp4 (mkConst ``BitVec.shiftLeft_eq_concat_of_lt) wExpr lhsExpr rhsExpr h
    return .done { expr := expr, proof? := some proof }
  else
    let expr := toExpr 0#w
    let h := Nat.mkDecideProofLe wExpr rhsExpr
    let proof := mkApp4 (mkConst ``BitVec.shiftLeft_eq_zero) wExpr lhsExpr rhsExpr h
    return .done { expr := expr, proof? := some proof }

builtin_simproc [bv_normalize] bv_concat_extract
    ((HAppend.hAppend (α := BitVec (no_index _)) (β := BitVec (no_index _)) (γ := BitVec (no_index _))
        (BitVec.extractLsb' _ _ _)
        (BitVec.extractLsb' _ _ _)))
    := fun e => do
  let_expr HAppend.hAppend _ _ _ _ lhsExpr rhsExpr := e | return .continue
  let_expr BitVec.extractLsb' wExpr lstartExpr llenExpr lhsVal := lhsExpr | return .continue
  let some lstart ← getNatValue? lstartExpr | return .continue
  let some llen ← getNatValue? llenExpr | return .continue
  let_expr BitVec.extractLsb' _ rstartExpr rlenExpr rhsVal := rhsExpr | return .continue
  let some rstart ← getNatValue? rstartExpr | return .continue
  let some rlen ← getNatValue? rlenExpr | return .continue
  if lhsVal != rhsVal then return .continue
  if lstart != rstart + rlen then return .continue
  let newLenExpr := toExpr (llen + rlen)
  let extract := mkApp4 (mkConst ``BitVec.extractLsb') wExpr rstartExpr newLenExpr lhsVal
  let expr := mkApp4 (mkConst ``BitVec.cast) newLenExpr newLenExpr (← mkEqRefl newLenExpr) extract
  let proof :=
    mkApp7
      (mkConst ``BitVec.extractLsb'_append_extractLsb'_eq_extractLsb')
      wExpr
      lstartExpr
      rstartExpr
      rlenExpr
      llenExpr
      lhsVal
      (← mkEqRefl lstartExpr)
  return .visit { expr := expr, proof? := some proof }

builtin_simproc [bv_normalize] bv_concat_not_extract
    ((HAppend.hAppend (α := BitVec (no_index _)) (β := BitVec (no_index _)) (γ := BitVec (no_index _))
        (Complement.complement (α := BitVec (no_index _)) (BitVec.extractLsb' _ _ _))
        (Complement.complement (α := BitVec (no_index _)) (BitVec.extractLsb' _ _ _))))
    := fun e => do
  let_expr HAppend.hAppend _ _ _ _ lhsExpr rhsExpr := e | return .continue
  let_expr Complement.complement _ _ lhsExpr := lhsExpr | return .continue
  let_expr Complement.complement _ _ rhsExpr := rhsExpr | return .continue
  let_expr BitVec.extractLsb' wExpr lstartExpr llenExpr lhsVal := lhsExpr | return .continue
  let some lstart ← getNatValue? lstartExpr | return .continue
  let some llen ← getNatValue? llenExpr | return .continue
  let_expr BitVec.extractLsb' _ rstartExpr rlenExpr rhsVal := rhsExpr | return .continue
  let some rstart ← getNatValue? rstartExpr | return .continue
  let some rlen ← getNatValue? rlenExpr | return .continue
  if lhsVal != rhsVal then return .continue
  if lstart != rstart + rlen then return .continue
  let newLenExpr := toExpr (llen + rlen)
  let extract := mkApp4 (mkConst ``BitVec.extractLsb') wExpr rstartExpr newLenExpr lhsVal
  let not := BitVec.mkComplement extract newLenExpr
  let expr := mkApp4 (mkConst ``BitVec.cast) newLenExpr newLenExpr (← mkEqRefl newLenExpr) not
  let proof :=
    mkApp7
      (mkConst ``BitVec.not_extractLsb'_append_not_extractLsb'_eq_not_extractLsb')
      wExpr
      lstartExpr
      rstartExpr
      rlenExpr
      llenExpr
      lhsVal
      (← mkEqRefl lstartExpr)
  return .visit { expr := expr, proof? := some proof }

builtin_simproc [bv_normalize] bv_elim_setWidth (BitVec.setWidth _ _) := fun e => do
  let_expr BitVec.setWidth oldWidthExpr newWidthExpr targetExpr := e | return .continue
  let some oldWidth ← getNatValue? oldWidthExpr | return .continue
  let some newWidth ← getNatValue? newWidthExpr | return .continue
  if newWidth ≤ oldWidth then
    let expr :=
      mkApp4
        (mkConst ``BitVec.extractLsb')
        oldWidthExpr
        (toExpr 0)
        newWidthExpr
        targetExpr
    let proof :=
      mkApp4
        (mkConst ``BitVec.setWidth_eq_extractLsb')
        oldWidthExpr
        targetExpr
        newWidthExpr
        (Nat.mkDecideProofLe newWidthExpr oldWidthExpr)
    return .visit { expr := expr, proof? := some proof }
  else
    let finalWidth := newWidth - oldWidth
    let lhs := toExpr 0#finalWidth
    let concat := BitVec.mkAppend
      lhs
      targetExpr
      (toExpr finalWidth)
      oldWidthExpr
      (toExpr (finalWidth + oldWidth))
    let expr :=
      mkApp4
        (mkConst ``BitVec.cast)
        newWidthExpr
        newWidthExpr
        (← mkEqRefl newWidthExpr)
        concat
    let proof :=
      mkApp4
        (mkConst ``BitVec.setWidth_eq_append)
        oldWidthExpr
        targetExpr
        newWidthExpr
        (Nat.mkDecideProofLe oldWidthExpr newWidthExpr)
    return .visit { expr := expr, proof? := some proof }

builtin_simproc [bv_normalize] bv_elim_signExtend (BitVec.signExtend _ _) := fun e => do
  let_expr BitVec.signExtend oldWidthExpr newWidthExpr targetExpr := e | return .continue
  let some oldWidth ← getNatValue? oldWidthExpr | return .continue
  let some newWidth ← getNatValue? newWidthExpr | return .continue
  if newWidth ≤ oldWidth then
    let expr :=
      mkApp4
        (mkConst ``BitVec.extractLsb')
        oldWidthExpr
        (toExpr 0)
        newWidthExpr
        targetExpr
    let proof :=
      mkApp4
        (mkConst ``Std.Tactic.BVDecide.Normalize.BitVec.signExtend_elim')
        oldWidthExpr
        targetExpr
        newWidthExpr
        (Nat.mkDecideProofLe newWidthExpr oldWidthExpr)
    return .visit { expr := expr, proof? := some proof }
  else
    let msb := mkApp2 (mkConst ``BitVec.msb) oldWidthExpr targetExpr
    let finalWidth := newWidth - oldWidth
    let finalWidthExpr := toExpr finalWidth
    let lhs :=
      mkApp4
        (mkConst ``cond [1])
        (mkApp (mkConst ``BitVec) finalWidthExpr)
        msb
        (toExpr (-1#finalWidth))
        (toExpr (0#finalWidth))
    let concat := BitVec.mkAppend
      lhs
      targetExpr
      finalWidthExpr
      oldWidthExpr
      (toExpr (finalWidth + oldWidth))
    let expr :=
      mkApp4
        (mkConst ``BitVec.cast)
        newWidthExpr
        newWidthExpr
        (← mkEqRefl newWidthExpr)
        concat
    let proof :=
      mkApp4
        (mkConst ``Std.Tactic.BVDecide.Normalize.BitVec.signExtend_elim)
        oldWidthExpr
        targetExpr
        newWidthExpr
        (Nat.mkDecideProofLe oldWidthExpr newWidthExpr)
    return .visit { expr := expr, proof? := some proof }

builtin_simproc [bv_normalize] bv_lt_allOnes_iff (BitVec.ult _ (BitVec.ofNat _ _)) := fun e => do
  let_expr BitVec.ult wExpr lhsExpr rhsExpr := e | return .continue
  let some ⟨w, rhs⟩ ← getBitVecValue? rhsExpr | return .continue
  if rhs != -1#w then return .continue
  let expr := mkApp (mkConst ``Bool.not) (BitVec.mkBEq lhsExpr (toExpr (-1#w)) wExpr)
  let proof := mkApp2 (mkConst ``Std.Tactic.BVDecide.Normalize.BitVec.ult_max') wExpr lhsExpr
  return .visit { expr := expr, proof? := some proof }

builtin_simproc [bv_normalize] bv_extract_concat
    (BitVec.extractLsb' _ _
      (HAppend.hAppend (γ := BitVec (no_index _)) (_ : BitVec _) (_ : BitVec _))) := fun e => do
  let_expr BitVec.extractLsb' _ startExpr lenExpr targetExpr := e | return .continue
  let_expr HAppend.hAppend lhsTypeExpr rhsTypeExpr _ _ lhsExpr rhsExpr := targetExpr | return .continue
  let_expr BitVec lhsWidthExpr := lhsTypeExpr | return .continue
  let_expr BitVec rhsWidthExpr := rhsTypeExpr | return .continue
  let some start ← getNatValue? startExpr | return .continue
  let some len ← getNatValue? lenExpr | return .continue
  let some rhsWidth ← getNatValue? rhsWidthExpr | return .continue
  if start + len ≤ rhsWidth then
    let expr := mkApp4 (mkConst ``BitVec.extractLsb') rhsWidthExpr startExpr lenExpr rhsExpr
    let proof :=
      mkApp7
        (mkConst ``BitVec.extractLsb'_append_eq_of_add_le)
        lhsWidthExpr
        rhsWidthExpr
        lhsExpr
        rhsExpr
        startExpr
        lenExpr
        (Nat.mkDecideProofLe (toExpr (start + len)) rhsWidthExpr)
    return .visit { expr := expr, proof? := some proof }
  else if rhsWidth ≤ start then
    let expr := mkApp4 (mkConst ``BitVec.extractLsb') lhsWidthExpr (toExpr (start - rhsWidth)) lenExpr lhsExpr
    let proof :=
      mkApp7
        (mkConst ``BitVec.extractLsb'_append_eq_of_le)
        lhsWidthExpr
        rhsWidthExpr
        lhsExpr
        rhsExpr
        startExpr
        lenExpr
        (Nat.mkDecideProofLe rhsWidthExpr startExpr)
    return .visit { expr := expr, proof? := some proof }
  else
    -- extract is not limited to side
    return .continue

builtin_simproc [bv_normalize] extract_add
    (BitVec.extractLsb' _ _ ((_ : BitVec _) + (_ : BitVec _))) := fun e => do
  let_expr BitVec.extractLsb' widthExpr startExpr lenExpr targetExpr := e | return .continue
  let_expr HAdd.hAdd _ _ _ _ lhsExpr rhsExpr := targetExpr | return .continue
  let some start ← getNatValue? startExpr | return .continue
  let some len ← getNatValue? lenExpr | return .continue
  let some width ← getNatValue? widthExpr | return .continue
  if !(start == 0 && len ≤ width) then return .continue

  let newLhsExpr := mkApp4 (mkConst ``BitVec.extractLsb') widthExpr startExpr lenExpr lhsExpr
  let newRhsExpr := mkApp4 (mkConst ``BitVec.extractLsb') widthExpr startExpr lenExpr rhsExpr
  let expr ← mkAdd newLhsExpr newRhsExpr
  let proof :=
    mkApp5
      (mkConst ``BitVec.extractLsb'_add)
      widthExpr
      lenExpr
      lhsExpr
      rhsExpr
      (Nat.mkDecideProofLe lenExpr widthExpr)
  return .visit { expr := expr, proof? := some proof }

builtin_simproc [bv_normalize] extract_mul
    (BitVec.extractLsb' _ _ ((_ : BitVec _) * (_ : BitVec _))) := fun e => do
  let_expr BitVec.extractLsb' widthExpr startExpr lenExpr targetExpr := e | return .continue
  let_expr HMul.hMul _ _ _ _ lhsExpr rhsExpr := targetExpr | return .continue
  let some start ← getNatValue? startExpr | return .continue
  let some len ← getNatValue? lenExpr | return .continue
  let some width ← getNatValue? widthExpr | return .continue
  if !(start == 0 && len ≤ width) then return .continue

  let newLhsExpr := mkApp4 (mkConst ``BitVec.extractLsb') widthExpr startExpr lenExpr lhsExpr
  let newRhsExpr := mkApp4 (mkConst ``BitVec.extractLsb') widthExpr startExpr lenExpr rhsExpr
  let expr ← mkMul newLhsExpr newRhsExpr
  let proof :=
    mkApp5
      (mkConst ``BitVec.extractLsb'_mul)
      widthExpr
      lenExpr
      lhsExpr
      rhsExpr
      (Nat.mkDecideProofLe lenExpr widthExpr)
  return .visit { expr := expr, proof? := some proof }

end Frontend.Normalize
end Lean.Elab.Tactic.BVDecide
