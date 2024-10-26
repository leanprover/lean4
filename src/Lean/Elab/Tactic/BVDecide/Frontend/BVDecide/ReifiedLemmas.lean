/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Lean.Elab.Tactic.BVDecide.Frontend.BVDecide.ReifiedBVLogical

/-!
Provides the logic for generating auxiliary lemmas during reification.
-/

namespace Lean.Elab.Tactic.BVDecide
namespace Frontend

open Std.Tactic.BVDecide
open Lean.Meta

/--
This function adds the two lemmas:
- `discrExpr = true → atomExpr = lhsExpr`
- `discrExpr = false → atomExpr = rhsExpr`
It assumes that `discrExpr`, `lhsExpr` and `rhsExpr` are the expressions corresponding to `discr`,
`lhs` and `rhs`. Furthermore it assumes that `atomExpr` is of the form
`if discrExpr = true then lhsExpr else rhsExpr`.
-/
def addIfLemmas (discr : ReifiedBVLogical) (atom lhs rhs : ReifiedBVExpr)
    (discrExpr atomExpr lhsExpr rhsExpr : Expr) : LemmaM Unit := do
  let some trueLemma ← mkIfTrueLemma discr atom lhs rhs discrExpr atomExpr lhsExpr rhsExpr | return ()
  LemmaM.addLemma trueLemma
  let some falseLemma ← mkIfFalseLemma discr atom lhs rhs discrExpr atomExpr lhsExpr rhsExpr | return ()
  LemmaM.addLemma falseLemma
where
  mkIfTrueLemma (discr : ReifiedBVLogical) (atom lhs rhs : ReifiedBVExpr)
      (discrExpr atomExpr lhsExpr rhsExpr : Expr) : M (Option SatAtBVLogical) :=
    mkIfLemma true discr atom lhs rhs discrExpr atomExpr lhsExpr rhsExpr

  mkIfFalseLemma (discr : ReifiedBVLogical) (atom lhs rhs : ReifiedBVExpr)
      (discrExpr atomExpr lhsExpr rhsExpr : Expr) : M (Option SatAtBVLogical) :=
    mkIfLemma false discr atom lhs rhs discrExpr atomExpr lhsExpr rhsExpr

  mkIfLemma (discrVal : Bool) (discr : ReifiedBVLogical) (atom lhs rhs : ReifiedBVExpr)
      (discrExpr atomExpr lhsExpr rhsExpr : Expr) : M (Option SatAtBVLogical) := do
    let resExpr := if discrVal then lhsExpr else rhsExpr
    let resValExpr := if discrVal then lhs else rhs
    let lemmaName :=
      if discrVal then
        ``Std.Tactic.BVDecide.Reflect.BitVec.if_true
      else
        ``Std.Tactic.BVDecide.Reflect.BitVec.if_false
    let discrValExpr := toExpr discrVal
    let discrVal ← ReifiedBVLogical.mkBoolConst discrVal

    let eqDiscrExpr ← mkAppM ``BEq.beq #[discrExpr, discrValExpr]
    let eqDiscr ← ReifiedBVLogical.mkGate discr discrVal discrExpr discrValExpr .beq

    let eqBVExpr ← mkAppM ``BEq.beq #[atomExpr, resExpr]
    let some eqBVPred ← ReifiedBVPred.mkBinPred atom resValExpr atomExpr resExpr .eq | return none
    let eqBV ← ReifiedBVLogical.ofPred eqBVPred

    let trueExpr := mkConst ``Bool.true
    let impExpr ← mkArrow (← mkEq eqDiscrExpr trueExpr) (← mkEq eqBVExpr trueExpr)
    let decideImpExpr ← mkAppOptM ``Decidable.decide #[some impExpr, none]
    let imp ← ReifiedBVLogical.mkGate eqDiscr eqBV eqDiscrExpr eqBVExpr .imp

    let proof := do
      let evalExpr ← ReifiedBVLogical.mkEvalExpr imp.expr
      let congrProof ← imp.evalsAtAtoms
      let lemmaProof := mkApp4 (mkConst lemmaName) (toExpr lhs.width) discrExpr lhsExpr rhsExpr
      return mkApp4
        (mkConst ``Std.Tactic.BVDecide.Reflect.Bool.lemma_congr)
        decideImpExpr
        evalExpr
        congrProof
        lemmaProof
    return some ⟨imp.bvExpr, proof, imp.expr⟩

/--
This function adds the two lemmas:
- `boolExpr = true → atomExpr = 1#1`
- `boolExpr = false → atomExpr = 0#1`
It assumes that `boolExpr` and `atomExpr` are the expressions corresponding to `bool` and `atom`.
Furthermore it assumes that `atomExpr` is of the form `BitVec.ofBool boolExpr`.
-/
def addOfBoolLemmas (bool : ReifiedBVLogical) (atom : ReifiedBVExpr) (boolExpr atomExpr : Expr) :
    LemmaM Unit := do
  let some ofBoolTrueLemma ← mkOfBoolTrueLemma bool atom boolExpr atomExpr | return ()
  LemmaM.addLemma ofBoolTrueLemma
  let some ofBoolFalseLemma ← mkOfBoolFalseLemma bool atom boolExpr atomExpr | return ()
  LemmaM.addLemma ofBoolFalseLemma
where
  mkOfBoolTrueLemma (bool : ReifiedBVLogical) (atom : ReifiedBVExpr) (boolExpr atomExpr : Expr) :
      M (Option SatAtBVLogical) := mkOfBoolLemma bool atom boolExpr atomExpr true 1#1

  mkOfBoolFalseLemma (bool : ReifiedBVLogical) (atom : ReifiedBVExpr) (boolExpr atomExpr : Expr) :
      M (Option SatAtBVLogical) := mkOfBoolLemma bool atom boolExpr atomExpr false 0#1

  mkOfBoolLemma (bool : ReifiedBVLogical) (atom : ReifiedBVExpr) (boolExpr atomExpr : Expr)
     (boolVal : Bool) (resVal : BitVec 1) : M (Option SatAtBVLogical) := do
    let lemmaName :=
      match boolVal with
      | .true => ``Std.Tactic.BVDecide.Reflect.BitVec.ofBool_true
      | .false => ``Std.Tactic.BVDecide.Reflect.BitVec.ofBool_false

    let boolValExpr := toExpr boolVal
    let boolVal ← ReifiedBVLogical.mkBoolConst boolVal
    let resExpr := toExpr resVal
    let resValExpr ← ReifiedBVExpr.mkBVConst resVal

    let eqBoolExpr ← mkAppM ``BEq.beq #[boolExpr, boolValExpr]
    let eqBool ← ReifiedBVLogical.mkGate bool boolVal boolExpr boolValExpr .beq

    let eqBVExpr ← mkAppM ``BEq.beq #[mkApp (mkConst ``BitVec.ofBool) boolExpr, resExpr]
    let some eqBVPred ← ReifiedBVPred.mkBinPred atom resValExpr atomExpr resExpr .eq | return none
    let eqBV ← ReifiedBVLogical.ofPred eqBVPred

    let trueExpr := mkConst ``Bool.true
    let impExpr ← mkArrow (← mkEq eqBoolExpr trueExpr) (← mkEq eqBVExpr trueExpr)
    let decideImpExpr ← mkAppOptM ``Decidable.decide #[some impExpr, none]
    let imp ← ReifiedBVLogical.mkGate eqBool eqBV eqBoolExpr eqBVExpr .imp

    let proof := do
      let evalExpr ← ReifiedBVLogical.mkEvalExpr imp.expr
      let congrProof ← imp.evalsAtAtoms
      let lemmaProof := mkApp (mkConst lemmaName) boolExpr
      return mkApp4
        (mkConst ``Std.Tactic.BVDecide.Reflect.Bool.lemma_congr)
        decideImpExpr
        evalExpr
        congrProof
        lemmaProof
    return some ⟨imp.bvExpr, proof, imp.expr⟩

end Frontend
end Lean.Elab.Tactic.BVDecide
