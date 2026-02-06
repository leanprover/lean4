/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module
prelude
public import Lean.Meta.Sym.Simp.SimpM
import Lean.Meta.Sym.AlphaShareBuilder
import Lean.Meta.Sym.InstantiateS
import Lean.Meta.Sym.InferType
import Lean.Meta.Sym.Simp.App
import Lean.Meta.SynthInstance
import Lean.Meta.WHNF
import Lean.Meta.AppBuilder
import Init.Sym.Lemmas
namespace Lean.Meta.Sym.Simp
open Internal

def simpIteCbv : Simproc := fun e => do
  let numArgs := e.getAppNumArgs
  if numArgs < 5 then return .rfl (done := true)
  propagateOverApplied e (numArgs - 5) fun e => do
    let_expr f@ite α c _ a b := e | return .rfl
    match (← simp c) with
    | .rfl _ =>
      if (← isTrueExpr c) then
        return .step a <| mkApp3 (mkConst ``ite_true f.constLevels!) α a b
      else if (← isFalseExpr  c) then
        return .step b <| mkApp3 (mkConst ``ite_false f.constLevels!) α a b
      else
        let .some inst' ← trySynthInstance (mkApp (mkConst ``Decidable) c) | return .rfl
        let inst' ← shareCommon inst'
        let toEval ← mkAppS₂ (mkConst ``Decidable.decide) c inst'
        let evalRes ← simp toEval
        match evalRes with
        | .rfl _ =>
          return .rfl (done := true)
        | .step v hv _ =>
          if (← isBoolTrueExpr v) then
            let h' := mkApp3 (mkConst ``eq_true_of_decide) c inst' hv
            let inst' := mkConst ``instDecidableTrue
            let c' ← getTrueExpr
            let h' := mkApp3 (e.replaceFn ``Sym.ite_cond_congr) c' inst' h'
            let ha := mkApp3 (mkConst ``ite_true f.constLevels!) α a b
            -- TODO: use the symbolic version
            let ha ← mkEqTrans h' ha
            return .step a ha (done := false)
          else if  (← isBoolFalseExpr v)  then
            let h' := mkApp3 (mkConst ``eq_false_of_decide) c inst' hv
            let inst' := mkConst ``instDecidableFalse
            let c' ← getFalseExpr
            let h' := mkApp3 (e.replaceFn ``Sym.ite_cond_congr) c' inst' h'
            let hb := mkApp3 (mkConst ``ite_false f.constLevels!) α a b
            --TODO: use the symbolic version
            let hb ← mkEqTrans h' hb
            return .step b hb (done := false)
          else
            return .rfl (done := true)
    | .step c' h _ =>
      if (← isTrueExpr c') then
        return .step a <| mkApp (e.replaceFn ``ite_cond_eq_true) h
      else if (← isFalseExpr c') then
        return .step b <| mkApp (e.replaceFn ``ite_cond_eq_false) h
      else
        let .some inst' ← trySynthInstance (mkApp (mkConst ``Decidable) c') | return .rfl
        let inst' ← shareCommon inst'
        let e' := e.getBoundedAppFn 4
        let e' ← mkAppS₄ e' c' inst' a b
        let h' := mkApp3 (e.replaceFn ``Sym.ite_cond_congr) c' inst' h
        return .step e' h' (done := true)

def simpDIteCbv : Simproc := fun e => do
  let numArgs := e.getAppNumArgs
  if numArgs < 5 then return .rfl (done := true)
  propagateOverApplied e (numArgs - 5) fun e => do
    let_expr f@dite α c _ a b := e | return .rfl
    match (← simp c) with
    | .rfl _ =>
      if (← isTrueExpr c) then
        let a' ← share <| a.betaRev #[mkConst ``True.intro]
        return .step a' <| mkApp3 (mkConst ``dite_true f.constLevels!) α a b
      else if (← isFalseExpr c) then
        let b' ← share <| b.betaRev #[mkConst ``not_false]
        return .step b' <| mkApp3 (mkConst ``dite_false f.constLevels!) α a b
      else
        let .some inst' ← trySynthInstance (mkApp (mkConst ``Decidable) c) | return .rfl
        let inst' ← shareCommon inst'
        let toEval ← mkAppS₂ (mkConst ``Decidable.decide) c inst'
        let evalRes ← simp toEval
        match evalRes with
        | .rfl _ => return .rfl (done := true)
        | .step v hv _ =>
          if  (← isBoolTrueExpr v) then
            let h' := mkApp3 (mkConst ``eq_true_of_decide) c inst' hv
            let inst' := mkConst ``instDecidableTrue
            let h ← shareCommon h'
            let c' ← getTrueExpr
            let a ← share <| mkLambda `h .default c' (a.betaRev #[mkApp4 (mkConst ``Eq.mpr_prop) c c' h (mkBVar 0)])
            let b ← share <| mkLambda `h .default (mkNot c') (b.betaRev #[mkApp4 (mkConst ``Eq.mpr_not) c c' h (mkBVar 0)])
            let h' := mkApp3 (e.replaceFn ``Sym.dite_cond_congr) c' inst' h
            let a' ← share <| a.betaRev #[mkConst ``True.intro]
            let ha := mkApp3 (mkConst ``dite_true f.constLevels!) α a b
            let ha ← mkEqTrans h' ha
            return .step a' ha
          else if  (← isBoolFalseExpr v)  then
            let h' := mkApp3 (mkConst ``eq_false_of_decide) c inst' hv
            let inst' := mkConst ``instDecidableFalse
            let h ← shareCommon h'
            let c' ← getFalseExpr
            let a ← share <| mkLambda `h .default c' (a.betaRev #[mkApp4 (mkConst ``Eq.mpr_prop) c c' h (mkBVar 0)])
            let b ← share <| mkLambda `h .default (mkNot c') (b.betaRev #[mkApp4 (mkConst ``Eq.mpr_not) c c' h (mkBVar 0)])
            let h' := mkApp3 (e.replaceFn ``Sym.dite_cond_congr) c' inst' h
            let b' ← share <| b.betaRev #[mkConst ``not_false]
            let hb := mkApp3 (mkConst ``dite_false f.constLevels!) α a b
            -- TODO: Use symbolic transitivity
            let hb ← mkEqTrans h' hb
            return .step b' hb
          else
            return .rfl (done := true)
    | .step c' h _ =>
      if (← isTrueExpr c') then
        let h' ← shareCommon <| mkOfEqTrueCore c h
        let a ← share <| a.betaRev #[h']
        return .step a <| mkApp (e.replaceFn ``dite_cond_eq_true) h
      else if (← isFalseExpr c') then
        let h' ← shareCommon <| mkOfEqFalseCore c h
        let b ← share <| b.betaRev #[h']
        return .step b <| mkApp (e.replaceFn ``dite_cond_eq_false) h
      else
        let .some inst' ← trySynthInstance (mkApp (mkConst ``Decidable) c') | return .rfl
        let inst' ← shareCommon inst'
        let e' := e.getBoundedAppFn 4
        let h ← shareCommon h
        let a ← share <| mkLambda `h .default c' (a.betaRev #[mkApp4 (mkConst ``Eq.mpr_prop) c c' h (mkBVar 0)])
        let b ← share <| mkLambda `h .default (mkNot c') (b.betaRev #[mkApp4 (mkConst ``Eq.mpr_not) c c' h (mkBVar 0)])
        let e' ← mkAppS₄ e' c' inst' a b
        let h' := mkApp3 (e.replaceFn ``Sym.dite_cond_congr) c' inst' h
        return .step e' h' (done := true)

end Lean.Meta.Sym.Simp
