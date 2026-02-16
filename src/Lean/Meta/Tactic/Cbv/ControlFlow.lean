/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module
prelude
public import Lean.Meta.Sym.Simp.SimpM
import Lean.Meta.Sym.Simp.Result
import Lean.Meta.Sym.Simp.Rewrite
import Lean.Meta.Sym.Simp.ControlFlow
import Lean.Meta.Sym.AlphaShareBuilder
import Lean.Meta.Sym.InstantiateS
import Lean.Meta.Sym.InferType
import Lean.Meta.Sym.Simp.App
import Lean.Meta.SynthInstance
import Lean.Meta.WHNF
import Lean.Meta.AppBuilder
import Init.Sym.Lemmas
import Lean.Meta.Tactic.Cbv.TheoremsLookup
namespace Lean.Meta.Sym.Simp
open Internal

public def simpIteCbv : Simproc := fun e => do
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
            let e' := e.getBoundedAppFn 4
            let e' ← mkAppS₄ e' c' inst' a b
            let h' := mkApp3 (e.replaceFn ``Sym.ite_cond_congr) c' inst' h'
            let ha := mkApp3 (mkConst ``ite_true f.constLevels!) α a b
            let ha ← mkEqTrans e e' h' a ha
            return .step a ha (done := false)
          else if  (← isBoolFalseExpr v)  then
            let h' := mkApp3 (mkConst ``eq_false_of_decide) c inst' hv
            let inst' := mkConst ``instDecidableFalse
            let c' ← getFalseExpr
            let e' := e.getBoundedAppFn 4
            let e' ← mkAppS₄ e' c' inst' a b
            let h' := mkApp3 (e.replaceFn ``Sym.ite_cond_congr) c' inst' h'
            let hb := mkApp3 (mkConst ``ite_false f.constLevels!) α a b
            let hb ← mkEqTrans e e' h' b hb
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
        return .step e' h'

public def simpDIteCbv : Simproc := fun e => do
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
            let e' := e.getBoundedAppFn 4
            let h ← shareCommon h'
            let c' ← getTrueExpr
            let a ← share <| mkLambda `h .default c' (a.betaRev #[mkApp4 (mkConst ``Eq.mpr_prop) c c' h (mkBVar 0)])
            let b ← share <| mkLambda `h .default (mkNot c') (b.betaRev #[mkApp4 (mkConst ``Eq.mpr_not) c c' h (mkBVar 0)])
            let e' ← mkAppS₄ e' c' inst' a b
            let h' := mkApp3 (e.replaceFn ``Sym.dite_cond_congr) c' inst' h
            let a' ← share <| a.betaRev #[mkConst ``True.intro]
            let ha := mkApp3 (mkConst ``dite_true f.constLevels!) α a b
            let ha ← mkEqTrans e e' h' a' ha
            return .step a' ha
          else if  (← isBoolFalseExpr v)  then
            let h' := mkApp3 (mkConst ``eq_false_of_decide) c inst' hv
            let inst' := mkConst ``instDecidableFalse
            let e' := e.getBoundedAppFn 4
            let h ← shareCommon h'
            let c' ← getFalseExpr
            let a ← share <| mkLambda `h .default c' (a.betaRev #[mkApp4 (mkConst ``Eq.mpr_prop) c c' h (mkBVar 0)])
            let b ← share <| mkLambda `h .default (mkNot c') (b.betaRev #[mkApp4 (mkConst ``Eq.mpr_not) c c' h (mkBVar 0)])
            let e' ← mkAppS₄ e' c' inst' a b
            let h' := mkApp3 (e.replaceFn ``Sym.dite_cond_congr) c' inst' h
            let b' ← share <| b.betaRev #[mkConst ``not_false]
            let hb := mkApp3 (mkConst ``dite_false f.constLevels!) α a b
            let hb ← mkEqTrans e e' h' b' hb
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
        return .step e' h'

end Lean.Meta.Sym.Simp

namespace Lean.Meta.Tactic.Cbv
open Lean.Meta.Sym.Simp

def tryMatchEquations (appFn : Name) : Simproc := fun e => do
  let thms ← getMatchTheorems appFn
  thms.rewrite (d := dischargeNone) e

public def reduceRecMatcher : Simproc := fun e => do
  if let some e' ← reduceRecMatcher? e then
    return .step e' (← Sym.mkEqRefl e')
  else
    return .rfl

def tryMatcher : Simproc := fun e => do
  unless e.isApp do
    return .rfl
  let some appFn := e.getAppFn.constName? | return .rfl
  let some info ← getMatcherInfo? appFn | return .rfl
  let start := info.numParams + 1
  let stop  := start + info.numDiscrs
  (simpAppArgRange · start stop)
    >> tryMatchEquations appFn
      <|> reduceRecMatcher
        <| e

def whnfSimproc : Simproc := fun e => do
  let r ← withAtLeastTransparency .default <| whnf e
  let r ← Sym.share r
  return .step r (← Sym.mkEqRefl r)

def simpDecideProp : Simproc := fun e => do
  let numArgs := e.getAppNumArgs
  if numArgs < 2 then return .rfl (done := true)
  propagateOverApplied e (numArgs - 2) fun e => do
    let_expr Decidable.decide p h := e | return .rfl
    match (← (whnfSimproc >> simp) h) with
    | .rfl _ =>
      return .rfl
    | .step e' _ _ =>
      let args := e'.getAppArgs
      if (e'.isAppOf ``isTrue) then
        let hp := args[1]!
        let proof := mkApp3 (mkConst ``decide_eq_true) p h hp
        return .step (← Sym.getBoolTrueExpr) proof
      else if (e'.isAppOf ``isFalse) then
        let hnp := args[1]!
        let proof := mkApp3 (mkConst ``decide_eq_false) p h hnp
        return .step (← Sym.getBoolFalseExpr) proof
      else
        return .rfl

/-
  Precondition: `e` is an application
-/
public def simpControlCbv : Simproc := fun e => do
  let .const declName _ := e.getAppFn | return .rfl
  if declName == ``ite then
    simpIteCbv e
  else if declName == ``cond then
    simpCond e
  else if declName == ``dite then
    simpDIteCbv e
  else if declName == ``Decidable.decide then
    simpDecideProp <| e
  else if declName == ``Decidable.rec then
    -- We force the rewrite in the last argument, so that we can unfold the `Decidable` instance.
    (simpInterlaced · #[false,false,true,true,true]) >> reduceRecMatcher <| e
  else
    tryMatcher e

end Lean.Meta.Tactic.Cbv
