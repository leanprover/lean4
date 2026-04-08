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
import Lean.Meta.Tactic.Cbv.Opaque
import Lean.Meta.Tactic.Cbv.CbvEvalExt
import Lean.Compiler.NoncomputableAttr
import Init.CbvSimproc
import Lean.Meta.Tactic.Cbv.CbvSimproc

/-!
# Control Flow Handling for Cbv

Cbv-specific simprocs for `ite`, `dite`, `cond`, `match`, `Decidable.rec`, and `Decidable.decide`.

The standard `Sym.Simp` control flow simprocs (`simpIte`, `simpDIte`) give up
when the condition does not reduce to `True` or `False` directly. The Cbv variants
(`simpIteCbv`, `simpDIteCbv`) go further: they evaluate `Decidable.decide` on the
condition and use `eq_true_of_decide` / `eq_false_of_decide` to take the
corresponding branch.
-/

namespace Lean.Meta.Sym.Simp
open Internal

def isCbvNoncomputable (p : Name) : CoreM Bool := do
  let evalLemmas ← Tactic.Cbv.getCbvEvalLemmas p
  return evalLemmas.isNone && Lean.isNoncomputable (← getEnv) p

/--
Attempts to synthesize `Decidable p` instance and guards against picking up a `noncomputable` instance
-/
def trySynthComputableInstance (p : Expr) : SymM <| Option Expr := do
  let .some inst' ← trySynthInstance (mkApp (mkConst ``Decidable) p) | return .none
  if (← inst'.getUsedConstants.anyM (isCbvNoncomputable ·)) then return .none
  shareCommon inst'

/-- Reduce `ite` by matching the `Decidable` instance for `isTrue`/`isFalse`. -/
def matchIteDecidable (f α c inst a b instToMatch : Expr) (fallback : SimpM Result) : SimpM Result := do
  match_expr instToMatch with
  | Decidable.isTrue _ hp =>
    return .step a <| mkApp6 (mkConst ``Sym.ite_true f.constLevels!) α c inst a b hp
  | Decidable.isFalse _ hnp =>
    return .step b <| mkApp6 (mkConst ``Sym.ite_false f.constLevels!) α c inst a b hnp
  | _ => fallback

/-- Like `matchIteDecidable`, but for the congruence case where `c` was simplified to `c'` with proof `h`. -/
def matchIteDecidableCongr (f α c inst a b c' h inst' : Expr) (fallback : SimpM Result) : SimpM Result := do
  match_expr inst' with
  | Decidable.isTrue _ hp =>
    return .step a <| mkApp8 (mkConst ``Sym.ite_true_congr f.constLevels!) α c inst a b c' h hp
  | Decidable.isFalse _ hnp =>
    return .step b <| mkApp8 (mkConst ``Sym.ite_false_congr f.constLevels!) α c inst a b c' h hnp
  | _ => fallback

/-- Simplify the `Decidable` instance, then try `simpIteDecidable`. -/
def simpAndMatchIteDecidable (f α c inst a b : Expr) (fallback : SimpM Result) : SimpM Result := do
  -- Propagate cd from `simp inst`: in another context the instance might simplify differently.
  match (← simp inst) with
  | .rfl _ cd =>
    let r ← matchIteDecidable f α c inst a b inst fallback
    return if cd && !r.isContextDependent then r.withContextDependent else r
  | .step inst' _ _ cd =>
    let r ← matchIteDecidable f α c inst a b inst' fallback
    return if cd && !r.isContextDependent then r.withContextDependent else r

/-- Like `simpAndMatchIteDecidable`, but for the congruence case where `c` was simplified to `c'`. -/
def simpAndMatchIteDecidableCongr (f α c inst a b c' h inst' : Expr) (fallback : SimpM Result) : SimpM Result := do
  match (← simp inst') with
  | .rfl _ cd =>
    let r ← matchIteDecidableCongr f α c inst a b c' h inst' fallback
    return if cd && !r.isContextDependent then r.withContextDependent else r
  | .step inst'' _ _ cd =>
    let r ← matchIteDecidableCongr f α c inst a b c' h inst'' fallback
    return if cd && !r.isContextDependent then r.withContextDependent else r

/-- Like `simpIte` but also evaluates `Decidable.decide` when the condition does not
reduce to `True`/`False` directly. -/
builtin_cbv_simproc ↓ simpIteCbv (@ite _ _ _ _ _) := fun e => do
  let numArgs := e.getAppNumArgs
  if numArgs < 5 then return .rfl (done := true)
  propagateOverApplied e (numArgs - 5) fun e => do
    let_expr f@ite α c inst a b := e | return .rfl
    -- See Sym.Simp.ControlFlow.simpIte for why cd is propagated to all branches.
    match (← simp c) with
    | .rfl _ cd =>
      if (← isTrueExpr c) then
        return .step a (mkApp3 (mkConst ``ite_true f.constLevels!) α a b) (contextDependent := cd)
      else if (← isFalseExpr c) then
        return .step b (mkApp3 (mkConst ``ite_false f.constLevels!) α a b) (contextDependent := cd)
      else
        simpAndMatchIteDecidable f α c inst a b do return mkRflResult (done := true) (contextDependent := cd)
    | .step c' h _ cd =>
      if (← isTrueExpr c') then
        return .step a (mkApp (e.replaceFn ``ite_cond_eq_true) h) (contextDependent := cd)
      else if (← isFalseExpr c') then
        return .step b (mkApp (e.replaceFn ``ite_cond_eq_false) h) (contextDependent := cd)
      else
        -- If we got stuck with simplifying `p` then let's try evaluating the original instance
        simpAndMatchIteDecidable f α c inst a b do
          -- If we get stuck here, maybe the problem is that we need to look at `Decidable c'`
          let inst' := mkApp4 (mkConst ``decidable_of_decidable_of_eq) c c' inst h
          simpAndMatchIteDecidableCongr f α c inst a b c' h inst' do
            -- If we fail, then we just rewrite `c` to `c'`
            let e' := e.getBoundedAppFn 4
            let e' ← mkAppS₄ e' c' inst' a b
            let h' := mkApp3 (e.replaceFn ``Sym.ite_cond_congr) c' inst' h
            return .step e' h' (done := true) (contextDependent := cd)

/-- Reduce `dite` by matching the `Decidable` instance for `isTrue`/`isFalse`. -/
def matchDIteDecidable (f α c inst a b instToMatch : Expr) (fallback : SimpM Result) : SimpM Result := do
  match_expr instToMatch with
  | Decidable.isTrue _ hp =>
    let a' ← share <| a.betaRev #[hp]
    return .step a' <| mkApp6 (mkConst ``Sym.dite_true f.constLevels!) α c inst a b hp
  | Decidable.isFalse _ hnp =>
    let b' ← share <| b.betaRev #[hnp]
    return .step b' <| mkApp6 (mkConst ``Sym.dite_false f.constLevels!) α c inst a b hnp
  | _ => fallback

/-- Like `matchDIteDecidable`, but for the congruence case where `c` was simplified to `c'` with proof `h`. -/
def matchDIteDecidableCongr (f α c inst a b c' h inst' : Expr) (fallback : SimpM Result) : SimpM Result := do
  match_expr inst' with
  | Decidable.isTrue _ hp =>
    let hp' := mkApp4 (mkConst ``Eq.mpr_prop) c c' h hp
    let a' ← share <| a.betaRev #[hp']
    return .step a' <| mkApp8 (mkConst ``Sym.dite_true_congr f.constLevels!) α c inst a b c' h hp
  | Decidable.isFalse _ hnp =>
    let hnp' := mkApp4 (mkConst ``Eq.mpr_not) c c' h hnp
    let b' ← share <| b.betaRev #[hnp']
    return .step b' <| mkApp8 (mkConst ``Sym.dite_false_congr f.constLevels!) α c inst a b c' h hnp
  | _ => fallback

/-- Simplify the `Decidable` instance, then try `simpDIteDecidable`. -/
def simpAndMatchDIteDecidable (f α c inst a b : Expr) (fallback : SimpM Result) : SimpM Result := do
  match (← simp inst) with
  | .rfl _ cd =>
    let r ← matchDIteDecidable f α c inst a b inst fallback
    return if cd && !r.isContextDependent then r.withContextDependent else r
  | .step inst' _ _ cd =>
    let r ← matchDIteDecidable f α c inst a b inst' fallback
    return if cd && !r.isContextDependent then r.withContextDependent else r

/-- Like `simpAndMatchDIteDecidable`, but for the congruence case where `c` was simplified to `c'`. -/
def simpAndMatchDIteDecidableCongr (f α c inst a b c' h inst' : Expr) (fallback : SimpM Result) : SimpM Result := do
  match (← simp inst') with
  | .rfl _ cd =>
    let r ← matchDIteDecidableCongr f α c inst a b c' h inst' fallback
    return if cd && !r.isContextDependent then r.withContextDependent else r
  | .step inst'' _ _ cd =>
    let r ← matchDIteDecidableCongr f α c inst a b c' h inst'' fallback
    return if cd && !r.isContextDependent then r.withContextDependent else r

/-- Like `simpDIte` but also evaluates `Decidable.decide` when the condition does not
reduce to `True`/`False` directly. -/
builtin_cbv_simproc ↓ simpDIteCbv (@dite _ _ _ _ _) := fun e => do
  let numArgs := e.getAppNumArgs
  if numArgs < 5 then return .rfl (done := true)
  propagateOverApplied e (numArgs - 5) fun e => do
    let_expr f@dite α c inst a b := e | return .rfl
    match (← simp c) with
    | .rfl _ cd =>
      if (← isTrueExpr c) then
        let a' ← share <| a.betaRev #[mkConst ``True.intro]
        return .step a' (mkApp3 (mkConst ``dite_true f.constLevels!) α a b) (contextDependent := cd)
      else if (← isFalseExpr c) then
        let b' ← share <| b.betaRev #[mkConst ``not_false]
        return .step b' (mkApp3 (mkConst ``dite_false f.constLevels!) α a b) (contextDependent := cd)
      else
        simpAndMatchDIteDecidable f α c inst a b do return mkRflResult (done := true) (contextDependent := cd)
    | .step c' h _ cd =>
      if (← isTrueExpr c') then
        let h' ← shareCommon <| mkOfEqTrueCore c h
        let a ← share <| a.betaRev #[h']
        return .step a (mkApp (e.replaceFn ``dite_cond_eq_true) h) (contextDependent := cd)
      else if (← isFalseExpr c') then
        let h' ← shareCommon <| mkOfEqFalseCore c h
        let b ← share <| b.betaRev #[h']
        return .step b (mkApp (e.replaceFn ``dite_cond_eq_false) h) (contextDependent := cd)
      else
        -- If we get stuck after simplifying `p` to `p'`, then we try to evaluate the original instance
        simpAndMatchDIteDecidable f α c inst a b do
          -- Otherwise, we make `Decidable c'` instance and try to evaluate it instead
          let inst' := mkApp4 (mkConst ``decidable_of_decidable_of_eq) c c' inst h
          simpAndMatchDIteDecidableCongr f α c inst a b c' h inst' do
            let e' := e.getBoundedAppFn 4
            let h ← shareCommon h
            let a ← share <| mkLambda `h .default c' (a.betaRev #[mkApp4 (mkConst ``Eq.mpr_prop) c c' h (mkBVar 0)])
            let b ← share <| mkLambda `h .default (mkNot c') (b.betaRev #[mkApp4 (mkConst ``Eq.mpr_not) c c' h (mkBVar 0)])
            let e' ← mkAppS₄ e' c' inst' a b
            let h' := mkApp3 (e.replaceFn ``Sym.dite_cond_congr) c' inst' h
            return .step e' h' (done := true) (contextDependent := cd)

/-- Reduce `decide` by matching the `Decidable` instance for `isTrue`/`isFalse`. -/
def matchDecideDecidable (p inst instToMatch : Expr) (fallback : SimpM Result) : SimpM Result := do
  match_expr instToMatch with
  | Decidable.isTrue _ hp =>
    return .step (← getBoolTrueExpr) <| mkApp3 (mkConst ``Sym.decide_isTrue) p inst hp
  | Decidable.isFalse _ hnp =>
    return .step (← getBoolFalseExpr) <| mkApp3 (mkConst ``Sym.decide_isFalse) p inst hnp
  | _ => fallback

/-- Like `simpDecideByInst`, but for the case where `p` was simplified to `p'` with proof `h`. -/
def matchDecideDecidableCongr (p p' h inst inst' : Expr) (fallback : SimpM Result) : SimpM Result := do
  match_expr inst' with
  | Decidable.isTrue _ hp =>
    return .step (← getBoolTrueExpr) <| mkApp5 (mkConst ``Sym.decide_isTrue_congr) p p' h inst hp
  | Decidable.isFalse _ hnp =>
    return .step (← getBoolFalseExpr) <| mkApp5 (mkConst ``Sym.decide_isFalse_congr) p p' h inst hnp
  | _ => fallback

/-- Simplify the `Decidable` instance, then try `simpDecideByInst`. -/
def simpAndMatchDecideDecidable (p inst : Expr) (fallback : SimpM Result) : SimpM Result := do
  match (← simp inst) with
  | .rfl _ cd =>
    let r ← matchDecideDecidable p inst inst fallback
    return if cd && !r.isContextDependent then r.withContextDependent else r
  | .step inst' _ _ cd =>
    let r ← matchDecideDecidable p inst inst' fallback
    return if cd && !r.isContextDependent then r.withContextDependent else r

/-- Like `simpDecideByInstWithFallback`, but for the case where `p` was simplified to `p'`. -/
def simpAndMatchDecideDecidableCongr (p p' h inst inst' : Expr) (fallback : SimpM Result) : SimpM Result := do
  match (← simp inst') with
  | .rfl _ cd =>
    let r ← matchDecideDecidableCongr p p' h inst inst' fallback
    return if cd && !r.isContextDependent then r.withContextDependent else r
  | .step inst'' _ _ cd =>
    let r ← matchDecideDecidableCongr p p' h inst inst'' fallback
    return if cd && !r.isContextDependent then r.withContextDependent else r

/-- Simplify `Decidable.decide` by simplifying the proposition and reducing the instance.

First simplifies the proposition `p`. If the result is `True` or `False`, produces the
corresponding boolean directly. Otherwise, simplifies the `Decidable` instance and matches
on `isTrue`/`isFalse` to determine the boolean value. When `p` simplified to a new `p'`
but the instance doesn't reduce to `isTrue`/`isFalse`, falls back to rebuilding
`decide p'` with a congruence proof. -/
builtin_cbv_simproc ↓ simpDecideCbv (@Decidable.decide _ _) := fun e => do
  let numArgs := e.getAppNumArgs
  if numArgs < 2 then return .rfl (done := true)
  propagateOverApplied e (numArgs - 2) fun e => do
    let_expr Decidable.decide p inst := e | return .rfl
    match (← simp p) with
    | .rfl _ cd =>
      if (← isTrueExpr p) then
        return .step (← getBoolTrueExpr) (mkApp (mkConst ``decide_true) inst) (contextDependent := cd)
      else if (← isFalseExpr p) then
        return .step (← getBoolFalseExpr) (mkApp (mkConst ``decide_false) inst) (contextDependent := cd)
      else
        simpAndMatchDecideDecidable p inst do return mkRflResult (done := true) (contextDependent := cd)
    | .step p' hp _ cd =>
      if (← isTrueExpr p') then
        return .step (← getBoolTrueExpr) (mkApp3 (mkConst ``Sym.decide_prop_eq_true) p inst hp) (contextDependent := cd)
      else if (← isFalseExpr p') then
        return .step (← getBoolFalseExpr) (mkApp3 (mkConst ``Sym.decide_prop_eq_false) p inst hp) (contextDependent := cd)
      else
        let inst' ← trySynthComputableInstance p'
        let inst' := inst'.getD <| mkApp4 (mkConst ``decidable_of_decidable_of_eq) p p' inst hp
        simpAndMatchDecideDecidableCongr p p' hp inst inst' do
          let res := (mkConst ``Decidable.decide)
          let res ← shareCommon res
          let res ← mkAppS₂ res p' inst'
          return .step res (mkApp5 (mkConst ``Decidable.decide.congr_simp) p p' hp inst inst') (done := true) (contextDependent := cd)

end Lean.Meta.Sym.Simp

namespace Lean.Meta.Tactic.Cbv
open Lean.Meta.Sym.Simp

/--
Run a `MetaM` computation with `whnf` blocked from unfolding `@[cbv_opaque]` definitions.
This prevents kernel-level reduction (used by `reduceRecMatcher?` and `reduceProj?`)
from bypassing the `@[cbv_opaque]` attribute.
-/
public def withCbvOpaqueGuard (x : MetaM α) : MetaM α := do
  let prev := (← readThe Meta.Context).canUnfold?
  withCanUnfoldPred (fun cfg info => do
    if (← isCbvOpaque info.name) then return false
    match prev with
    | some f => f cfg info
    | none =>
      -- Duplicates `canUnfoldDefault` from `Lean.Meta.GetUnfoldableConst` (private).
      match cfg.transparency with
      | .none => return false
      | .all  => return true
      | .default => return !(← isIrreducible info.name)
      | m =>
        let status ← getReducibilityStatus info.name
        if status == .reducible then return true
        else if m == .instances && status == .implicitReducible then return true
        else return false
  ) x

builtin_cbv_simproc ↓ simpCbvCond (@cond _ _ _) := simpCond

public def reduceRecMatcher : Simproc := fun e => do
  if let some e' ← withCbvOpaqueGuard <| reduceRecMatcher? e then
    trace[Meta.Tactic.cbv.rewrite] "recMatcher:{indentExpr e}\n==>{indentExpr e'}"
    return .step e' (← Sym.mkEqRefl e')
  else
    return .rfl

builtin_cbv_simproc ↓ simpDecidableRec (@Decidable.rec _ _ _ _ _) :=
  (simpInterlaced · #[false,false,false,false,true]) >> reduceRecMatcher

def tryMatchEquations (appFn : Name) : Simproc := fun e => do
  let thms ← getMatchTheorems appFn
  thms.rewrite (d := dischargeNone) e

/-- Dispatch control flow constructs to their specialized simprocs.
Precondition: `e` is an application. -/
public def tryMatcher : Simproc := fun e => do
  unless e.isApp do
    return .rfl
  let some appFn := e.getAppFn.constName? | return .rfl
  let some info ← getMatcherInfo? appFn | return .rfl
  let start := info.numParams + 1
  let stop  := start + info.numDiscrs
  let result ← (simpAppArgRange · start stop)
    >> tryMatchEquations appFn
      <|> reduceRecMatcher
        <| e
  if let .step e' .. := result then
    trace[Meta.Tactic.cbv.controlFlow] "match `{appFn}`:{indentExpr e}\n==>{indentExpr e'}"
  return result

end Lean.Meta.Tactic.Cbv
