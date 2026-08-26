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

namespace Lean.Meta.Tactic.Cbv

/--
Run a `MetaM` computation with `whnf` blocked from unfolding `@[cbv_opaque]` definitions.
This prevents kernel-level reduction (used by `reduceRecMatcher?` and `reduceProj?`)
from bypassing the `@[cbv_opaque]` attribute.
-/
public def withCbvOpaqueGuard (x : MetaM α) : MetaM α := do
  let prevCustomCanUnfoldPredicate? := (← readThe Meta.Context).customCanUnfoldPredicate?
  let prevCanUnfoldPredicateConfig := (← readThe Meta.Context).config.canUnfoldPredicateConfig
  withCanUnfoldPred (fun cfg info => do
    if (← isCbvOpaque info.name) then return false
    match prevCustomCanUnfoldPredicate? with
    | .some f => f cfg info
    | .none =>
      match prevCanUnfoldPredicateConfig with
      | .default => canUnfoldDefault cfg info
      | .atMatcher => canUnfoldAtMatcher cfg info
  ) x

end Lean.Meta.Tactic.Cbv

namespace Lean.Meta.Sym.Simp
open Lean.Meta.Sym.Internal

/--
Given `inst : Decidable p`, returns a result for `p = p'` and the corresponding new instance
for `Decidable p'`.
-/
def rewriteDecidableInstance (inst : Expr) : SimpM (Result × Expr) :=
  inst.withApp fun fn args => do
    if args.isEmpty then
      return (.rfl, inst)
    let ty ← Meta.inferType fn
    let p ← forallTelescopeReducing (whnfType := true) ty fun vars body => do←
      let_expr Decidable p := body | return (.rfl, inst)
      unless vars.size = args.size do
        -- this *feels* unreachable but just to be sure
        return (.rfl, inst)
      mkLambdaFVars vars p
    let p ← shareCommon p
    let res ← simpAppArgRange (← mkAppNS p args) 0 args.size
    match res with
    | .rfl .. => return (res, inst)
    | .step e' proof done cd =>
      -- We assume that the function stayed the same
      let revArgs := e'.getAppRevArgs
      return (.step (← betaRevS p revArgs) proof done cd, mkAppRev fn revArgs)

/-- Reduce `ite` by matching the `Decidable` instance for `isTrue`/`isFalse`. -/
def matchIteDecidable (f α c inst a b instToMatch : Expr) (fallback : SimpM Result) : SimpM Result := do
  match_expr instToMatch with
  | Decidable.intro _ bool hp =>
    match_expr bool with
    | Bool.true =>
      return .step a <| mkApp6 (mkConst ``Sym.ite_true f.constLevels!) α c inst a b hp
    | Bool.false =>
      return .step b <| mkApp6 (mkConst ``Sym.ite_false f.constLevels!) α c inst a b hp
    | _ => fallback
  | _ => fallback

/-- Like `matchIteDecidable`, but for the congruence case where `c` was simplified to `c'` with proof `h`. -/
def matchIteDecidableCongr (f α c inst a b c' h inst' : Expr) (fallback : SimpM Result) : SimpM Result := do
  match_expr inst' with
  | Decidable.intro _ bool hp =>
    match_expr bool with
    | Bool.true =>
        return .step a <| mkApp8 (mkConst ``Sym.ite_true_congr f.constLevels!) α c inst a b c' h hp
    | Bool.false =>
      return .step b <| mkApp8 (mkConst ``Sym.ite_false_congr f.constLevels!) α c inst a b c' h hp
    | _ => fallback
  | _ => fallback

/-- Simplify the `Decidable` instance, then try `simpIteDecidable`. -/
def simpAndMatchIteDecidable (f α c inst a b : Expr) (fallback : SimpM Result) : SimpM Result := do
  let reduced ← Tactic.Cbv.withCbvOpaqueGuard <| withImplicit <| project? inst 0
  match reduced with
  | some reduced =>
    let decide := mkApp2 (mkConst ``decide) c inst
    let reduced ← share reduced
    let refl := mkApp2 (.const ``Eq.refl [1]) (mkConst ``Bool) reduced
    let result ← simp reduced
    let result ← mkEqTransResult decide reduced refl result
    let .step bool hbool _ cd := result | unreachable!
    match_expr bool with
    | Bool.true =>
      return .step a (mkApp6 (mkConst ``Sym.ite_of_decide_eq_true f.constLevels!) α c inst a b hbool) (contextDependent := cd)
    | Bool.false =>
      return .step b (mkApp6 (mkConst ``Sym.ite_of_decide_eq_false f.constLevels!) α c inst a b hbool) (contextDependent := cd)
    | _ => fallback
  | none =>
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
  let reduced ← Tactic.Cbv.withCbvOpaqueGuard <| withImplicit <| project? inst' 0
  match reduced with
  | some reduced =>
    let decide := mkApp2 (mkConst ``decide) c' inst'
    let reduced ← share reduced
    let refl := mkApp2 (.const ``Eq.refl [1]) (mkConst ``Bool) reduced
    let result ← simp reduced
    let result ← mkEqTransResult decide reduced refl result
    let .step bool hbool _ cd := result | unreachable!
    match_expr bool with
    | Bool.true =>
      return .step a (mkApp9 (mkConst ``Sym.ite_of_decide_eq_true_congr f.constLevels!) α c inst a b c' h inst' hbool) (contextDependent := cd)
    | Bool.false =>
      return .step b (mkApp9 (mkConst ``Sym.ite_of_decide_eq_false_congr f.constLevels!) α c inst a b c' h inst' hbool) (contextDependent := cd)
    | _ => fallback
  | none =>
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
        return .step a (mkApp (e.replaceFn ``ite_eq_left_of_eq_true) h) (contextDependent := cd)
      else if (← isFalseExpr c') then
        return .step b (mkApp (e.replaceFn ``ite_eq_right_of_eq_false) h) (contextDependent := cd)
      else
        let (condRes, inst') ← rewriteDecidableInstance inst
        match condRes with
        | .rfl _ cd =>
          simpAndMatchIteDecidable f α c inst a b do return mkRflResult (done := true) (contextDependent := cd)
        | .step c' h _ cd =>
          simpAndMatchIteDecidableCongr f α c inst a b c' h inst' do
            let e' := e.getBoundedAppFn 4
            let e' ← mkAppS₄ e' c' inst' a b
            let h' := mkApp3 (e.replaceFn ``Sym.ite_cond_congr) c' inst' h
            return .step e' h' (done := true) (contextDependent := cd)

/-- Reduce `dite` by matching the `Decidable` instance for `isTrue`/`isFalse`. -/
def matchDIteDecidable (f α c inst a b instToMatch : Expr) (fallback : SimpM Result) : SimpM Result := do
  match_expr instToMatch with
  | Decidable.intro _ bool hp =>
    match_expr bool with
    | Bool.true =>
      let a' ← share <| a.betaRev #[hp]
      return .step a' <| mkApp6 (mkConst ``Sym.dite_true f.constLevels!) α c inst a b hp
    | Bool.false =>
      let b' ← share <| b.betaRev #[hp]
      return .step b' <| mkApp6 (mkConst ``Sym.dite_false f.constLevels!) α c inst a b hp
    | _ => fallback
  | _ => fallback

/-- Like `matchDIteDecidable`, but for the congruence case where `c` was simplified to `c'` with proof `h`. -/
def matchDIteDecidableCongr (f α c inst a b c' h inst' : Expr) (fallback : SimpM Result) : SimpM Result := do
  match_expr inst' with
  | Decidable.intro _ bool hp =>
    match_expr bool with
    | Bool.true =>
      let hp' := mkApp4 (mkConst ``Eq.mpr_prop) c c' h hp
      let a' ← share <| a.betaRev #[hp']
      return .step a' <| mkApp8 (mkConst ``Sym.dite_true_congr f.constLevels!) α c inst a b c' h hp
    | Bool.false =>
      let hnp' := mkApp4 (mkConst ``Eq.mpr_not) c c' h hp
      let b' ← share <| b.betaRev #[hnp']
      return .step b' <| mkApp8 (mkConst ``Sym.dite_false_congr f.constLevels!) α c inst a b c' h hp
    | _ => fallback
  | _ => fallback

/-- Simplify the `Decidable` instance, then try `simpDIteDecidable`. -/
def simpAndMatchDIteDecidable (f α c inst a b : Expr) (fallback : SimpM Result) : SimpM Result := do
  let reduced ← Tactic.Cbv.withCbvOpaqueGuard <| withImplicit <| project? inst 0
  match reduced with
  | some reduced =>
    let decide := mkApp2 (mkConst ``decide) c inst
    let reduced ← share reduced
    let refl := mkApp2 (.const ``Eq.refl [1]) (mkConst ``Bool) reduced
    let result ← simp reduced
    let result ← mkEqTransResult decide reduced refl result
    let .step bool hbool _ cd := result | unreachable!
    match_expr bool with
    | Bool.true =>
      let h ← shareCommon <| mkApp3 (mkConst ``of_decide_eq_true) c inst hbool
      let a' ← share <| a.betaRev #[h]
      return .step a' (mkApp6 (mkConst ``Sym.dite_true f.constLevels!) α c inst a b h) (contextDependent := cd)
    | Bool.false =>
      let h ← shareCommon <| mkApp3 (mkConst ``of_decide_eq_false) c inst hbool
      let b' ← share <| b.betaRev #[h]
      return .step b' (mkApp6 (mkConst ``Sym.dite_false f.constLevels!) α c inst a b h) (contextDependent := cd)
    | _ => fallback
  | none =>
    match (← simp inst) with
    | .rfl _ cd =>
      let r ← matchDIteDecidable f α c inst a b inst fallback
      return if cd && !r.isContextDependent then r.withContextDependent else r
    | .step inst' _ _ cd =>
      let r ← matchDIteDecidable f α c inst a b inst' fallback
      return if cd && !r.isContextDependent then r.withContextDependent else r

/-- Like `simpAndMatchDIteDecidable`, but for the congruence case where `c` was simplified to `c'`. -/
def simpAndMatchDIteDecidableCongr (f α c inst a b c' h inst' : Expr) (fallback : SimpM Result) : SimpM Result := do
  let reduced ← Tactic.Cbv.withCbvOpaqueGuard <| withImplicit <| project? inst' 0
  match reduced with
  | some reduced =>
    let decide := mkApp2 (mkConst ``decide) c' inst'
    let reduced ← share reduced
    let refl := mkApp2 (.const ``Eq.refl [1]) (mkConst ``Bool) reduced
    let result ← simp reduced
    let result ← mkEqTransResult decide reduced refl result
    let .step bool hbool _ cd := result | unreachable!
    match_expr bool with
    | Bool.true =>
      let hc' ← shareCommon <| mkApp3 (mkConst ``of_decide_eq_true) c' inst' hbool
      let hc := mkApp4 (mkConst ``Eq.mpr_prop) c c' h hc'
      let a' ← share <| a.betaRev #[hc]
      return .step a' (mkApp8 (mkConst ``Sym.dite_true_congr f.constLevels!) α c inst a b c' h hc') (contextDependent := cd)
    | Bool.false =>
      let hc' ← shareCommon <| mkApp3 (mkConst ``of_decide_eq_false) c' inst' hbool
      let hc := mkApp4 (mkConst ``Eq.mpr_not) c c' h hc'
      let b' ← share <| b.betaRev #[hc]
      return .step b' (mkApp8 (mkConst ``Sym.dite_false_congr f.constLevels!) α c inst a b c' h hc') (contextDependent := cd)
    | _ => fallback
  | none =>
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
        return .step a (mkApp (e.replaceFn ``dite_eq_left_of_eq_true) h) (contextDependent := cd)
      else if (← isFalseExpr c') then
        let h' ← shareCommon <| mkOfEqFalseCore c h
        let b ← share <| b.betaRev #[h']
        return .step b (mkApp (e.replaceFn ``dite_eq_right_of_eq_false) h) (contextDependent := cd)
      else
        let (condRes, inst') ← rewriteDecidableInstance inst
        match condRes with
        | .rfl _ cd =>
          simpAndMatchDIteDecidable f α c inst a b do return mkRflResult (done := true) (contextDependent := cd)
        | .step c' h _ cd =>
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
  | Decidable.intro _ bool hp =>
    match_expr bool with
    | Bool.true =>
      return .step (← getBoolTrueExpr) <| mkApp3 (mkConst ``Sym.decide_isTrue) p inst hp
    | Bool.false =>
      return .step (← getBoolFalseExpr) <| mkApp3 (mkConst ``Sym.decide_isFalse) p inst hp
    | _ => fallback
  | _ => fallback

/-- Like `simpDecideByInst`, but for the case where `p` was simplified to `p'` with proof `h`. -/
def matchDecideDecidableCongr (p p' h inst inst' : Expr) (fallback : SimpM Result) : SimpM Result := do
  match_expr inst' with
  | Decidable.intro _ bool hp =>
    match_expr bool with
    | Bool.true =>
      return .step (← getBoolTrueExpr) <| mkApp5 (mkConst ``Sym.decide_isTrue_congr) p p' h inst hp
    | Bool.false =>
      return .step (← getBoolFalseExpr) <| mkApp5 (mkConst ``Sym.decide_isFalse_congr) p p' h inst hp
    | _ => fallback
  | _ => fallback

/-- Simplify the `Decidable` instance, then try `simpDecideByInst`. -/
def simpAndMatchDecideDecidable (p inst : Expr) (fallback : SimpM Result) : SimpM Result := do
  let reduced ← Tactic.Cbv.withCbvOpaqueGuard <| withImplicit <| project? inst 0
  match reduced with
  | some reduced =>
    let reduced ← share reduced
    let refl := mkApp2 (.const ``Eq.refl [1]) (mkConst ``Bool) reduced
    return .step reduced refl
  | none =>
    match (← simp inst) with
    | .rfl _ cd =>
      let r ← matchDecideDecidable p inst inst fallback
      return if cd && !r.isContextDependent then r.withContextDependent else r
    | .step inst' _ _ cd =>
      let r ← matchDecideDecidable p inst inst' fallback
      return if cd && !r.isContextDependent then r.withContextDependent else r

/-- Like `simpDecideByInstWithFallback`, but for the case where `p` was simplified to `p'`. -/
def simpAndMatchDecideDecidableCongr (p p' h inst inst' : Expr) (fallback : SimpM Result) : SimpM Result := do
  let reduced ← Tactic.Cbv.withCbvOpaqueGuard <| withImplicit <| project? inst' 0
  match reduced with
  | some reduced =>
    let reduced ← share reduced
    let refl := mkApp2 (.const ``Eq.refl [1]) (mkConst ``Bool) reduced
    return .step reduced <| mkApp7 (mkConst ``Sym.decide_eq_congr) p p' h inst inst' reduced refl
  | none =>
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
        let (condRes, inst') ← rewriteDecidableInstance inst
        match condRes with
        | .rfl _ cd =>
          simpAndMatchDecideDecidable p inst do return mkRflResult (done := true) (contextDependent := cd)
        | .step p' hp _ cd =>
          simpAndMatchDecideDecidableCongr p p' hp inst inst' do
            let res := (mkConst ``Decidable.decide)
            let res ← shareCommon res
            let res ← mkAppS₂ res p' inst'
            return .step res (mkApp5 (mkConst ``Decidable.decide.congr_simp) p p' hp inst inst') (done := true) (contextDependent := cd)

end Lean.Meta.Sym.Simp

namespace Lean.Meta.Tactic.Cbv
open Lean.Meta.Sym.Simp

builtin_cbv_simproc ↓ simpCbvCond (@cond _ _ _) := simpCond

public def reduceRecMatcher : Simproc := fun e => do
  if let some e' ← withCbvOpaqueGuard <| reduceRecMatcher? e then
    trace[Meta.Tactic.cbv.rewrite] "recMatcher:{indentExpr e}\n==>{indentExpr e'}"
    return .step e' (← Sym.mkEqRefl e')
  else
    return .rfl

builtin_cbv_simproc ↓ simpDecidableRec (@Decidable.rec _ _ _ _) :=
  (simpInterlaced · #[false,false,false,true]) >> reduceRecMatcher

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
