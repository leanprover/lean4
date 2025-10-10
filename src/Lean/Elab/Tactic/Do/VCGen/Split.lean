/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Lean.Meta.Tactic.FunInd
public import Lean.Meta.Match.MatcherApp.Transform
import Lean.Meta.Tactic.Simp.Rewrite

public section

namespace Lean.Elab.Tactic.Do

open Lean Elab Tactic Meta

inductive SplitInfo where
  | ite (e : Expr)
  | dite (e : Expr)
  | matcher (matcherApp : MatcherApp)
  deriving Inhabited

namespace SplitInfo

def resTy (info : SplitInfo) : Option Expr := match info with
  | ite e => e.getArg! 0
  | dite e => e.getArg! 0
  -- For a matcher, the motive has type `(discr1 : α) → ... → (discrN : α) → Type`.
  -- We want to return `Type` component and fail if it depends on any of the discriminant values.
  | matcher matcherApp => do
    let motive := matcherApp.motive
    let e : Expr ← Nat.repeat (n := matcherApp.discrInfos.size) (a := some motive) fun e =>
      match e with
        | some (.lam _ _ e _) => e
        | _ => none
    unless e.looseBVarRange = motive.looseBVarRange do none
    return e

/--
A list of pairs `(numParams, alt)` per match alternative, where `numParams` is the
number of parameters of the alternative and `alt` is the alternative.
-/
def altInfos (info : SplitInfo) : Array (Nat × Expr) := match info with
  | ite e => #[(0, e.getArg! 3), (0, e.getArg! 4)]
  | dite e => #[(1, e.getArg! 3), (1, e.getArg! 4)]
  | matcher matcherApp => matcherApp.altNumParams.mapIdx fun idx numParams =>
      (numParams, matcherApp.alts[idx]!)

def splitWithConstantMotive
  {n} [MonadLiftT MetaM n] [MonadControlT MetaM n] [Monad n] [MonadError n] [MonadEnv n] [MonadLog n]
  [AddMessageContext n] [MonadOptions n]
  (info : SplitInfo) (resTy : Expr) (onAlt : Name → Nat → Array Expr → n Expr) (useSplitter := false) : n Expr := match info with
  | ite e => do
    let u ← getLevel resTy
    let c := e.getArg! 1
    let h := e.getArg! 2
    if useSplitter then -- dite is the "splitter" for ite
      let n ← liftMetaM <| mkFreshUserName `h
      let t ← withLocalDecl n .default c fun h => do mkLambdaFVars #[h] (← onAlt `isTrue 0 #[])
      let e ← withLocalDecl n .default (mkNot c) fun h => do mkLambdaFVars #[h] (← onAlt `isFalse 1 #[])
      return mkApp5 (mkConst ``_root_.dite [u]) resTy c h t e
    else
      let t ← onAlt `isTrue 0 #[]
      let e ← onAlt `isFalse 1 #[]
      return mkApp5 (mkConst ``_root_.ite [u]) resTy c h t e
  | dite e => do
    let u ← getLevel resTy
    let c := e.getArg! 1
    let h := e.getArg! 2
    let n ← liftMetaM <| mkFreshUserName `h
    let t ← withLocalDecl n .default c fun h => do mkLambdaFVars #[h] (← onAlt `isTrue 0 #[h])
    let e ← withLocalDecl n .default (mkNot c) fun h => do mkLambdaFVars #[h] (← onAlt `isFalse 1 #[h])
    return mkApp5 (mkConst ``_root_.dite [u]) resTy c h t e
  | matcher matcherApp => do
    (·.toExpr) <$> matcherApp.transform
      (useSplitter := useSplitter) (addEqualities := useSplitter) -- (freshenNames := true)
      (onMotive := fun _xs _motive => pure resTy)
      (onAlt := fun idx _ty params _alt => onAlt ((`h).appendIndexAfter (idx+1)) idx params)

def simpDiscrs? (info : SplitInfo) (e : Expr) : SimpM (Option Simp.Result) := match info with
  | dite _ | ite _ => return none -- Tricky because we need to simultaneously rewrite  `[Decidable c]`
  | matcher matcherApp => Simp.simpMatchDiscrs? matcherApp.toMatcherInfo e

end SplitInfo

def getSplitInfo? (e : Expr) : MetaM (Option SplitInfo) := do
  if e.isAppOf ``ite then
    return some (SplitInfo.ite e)
  if e.isAppOf ``dite then
    return some (SplitInfo.dite e)
  if let .some matcherApp ← matchMatcherApp? (alsoCasesOn := true) e then
    return some (SplitInfo.matcher matcherApp)
  else
    return none

def rwIfOrMatcher (idx : Nat) (e : Expr) : MetaM Simp.Result := do
  if e.isAppOf ``ite || e.isAppOf ``dite then
    let c := e.getArg! 1
    let c := if idx = 0 then c else mkNot c
    let .some fv ← findLocalDeclWithType? c
      | throwError "Failed to find proof for if condition {c}"
    FunInd.rwIfWith (mkFVar fv) e
  else
    FunInd.rwMatcher idx e
