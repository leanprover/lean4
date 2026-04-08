/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Lean.Meta.Tactic.Simp.Types
public import Lean.Meta.Match.MatcherApp.Transform
public import Lean.Data.Array
import Lean.Meta.Match.Rewrite
import Lean.Meta.Tactic.Simp.Rewrite
import Lean.Meta.Tactic.Assumption

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

/-- The expression represented by a `SplitInfo`. -/
def expr : SplitInfo → Expr
  | .ite e => e
  | .dite e => e
  | .matcher matcherApp => matcherApp.toExpr

/--
Introduces fvars for all varying parts of a `SplitInfo` and provides the abstract
`SplitInfo` and fvars to the continuation.

For `ite`/`dite`, introduces `c : Prop`, `dec : Decidable c`, `t : mα` (or `t : c → mα`),
`e : mα` (or `e : ¬c → mα`).
For `matcher`, introduces discriminant fvars and alternative fvars, builds a non-dependent
motive `fun _ ... _ => mα`, and adjusts matcher universe levels.

The abstract `SplitInfo` satisfies `abstractInfo.expr = abstractProgram`.

For `matcher`, the abstract `MatcherApp` stores eta-expanded fvar alts so that
`splitWith`/`matcherApp.transform` can `instantiateLambda` them directly (no patching needed).
Since eta-expanded alts like `fun n => alt n` can cause expensive higher-order unification in
backward rule patterns, callers building backward rules should eta-reduce them first (e.g.
via `Expr.eta` on the alt arguments of `abstractInfo.expr`).
-/
def withAbstract {n} {α} [MonadLiftT MetaM n] [MonadControlT MetaM n] [Monad n] [Inhabited α]
    (info : SplitInfo) (resTy : Expr)
    (k : (abstractInfo : SplitInfo) → (splitFVars : Array Expr) → n α) : n α :=
  match info with
  | .ite _ =>
    withLocalDeclD `c (mkSort 0) fun c =>
    withLocalDeclD `dec (mkApp (mkConst ``Decidable) c) fun dec =>
    withLocalDeclD `t resTy fun t =>
    withLocalDeclD `e resTy fun e => do
    let u ← liftMetaM <| getLevel resTy
    k (.ite <| mkApp5 (mkConst ``_root_.ite [u]) resTy c dec t e) #[c, dec, t, e]
  | .dite _ =>
    withLocalDeclD `c (mkSort 0) fun c =>
    withLocalDeclD `dec (mkApp (mkConst ``Decidable) c) fun dec => do
    let tTy ← liftMetaM <| mkArrow c resTy
    let eTy ← liftMetaM <| mkArrow (mkNot c) resTy
    withLocalDeclD `t tTy fun t =>
    withLocalDeclD `e eTy fun e => do
    let u ← liftMetaM <| getLevel resTy
    k (.dite <| mkApp5 (mkConst ``_root_.dite [u]) resTy c dec t e) #[c, dec, t, e]
  | .matcher matcherApp => do
    let discrNamesTypes ← matcherApp.discrs.mapIdxM fun i discr => do
      return ((`discr).appendIndexAfter (i+1), ← liftMetaM <| inferType discr)
    withLocalDeclsDND discrNamesTypes fun discrs => do
    -- Non-dependent motive: fun _ ... _ => mα
    let motive ← liftMetaM <| lambdaTelescope matcherApp.motive fun motiveArgs _ =>
      mkLambdaFVars motiveArgs resTy
    -- The matcher's universe levels include a `uElimPos` slot for the elimination target level.
    -- Our abstract motive `fun _ ... _ => mα` may target a different level than the original
    -- dependent motive, so we update `matcherLevels[uElimPos]` to `getLevel mα`.
    let matcherLevels ← match matcherApp.uElimPos? with
      | none => pure matcherApp.matcherLevels
      | some pos => do
        let uElim ← liftMetaM <| getLevel resTy
        pure <| matcherApp.matcherLevels.set! pos uElim
    -- Build partial application to infer alt types
    let matcherPartial := mkAppN (mkConst matcherApp.matcherName matcherLevels.toList) matcherApp.params
    let matcherPartial := mkApp matcherPartial motive
    let matcherPartial := mkAppN matcherPartial discrs
    let origAltTypes ← liftMetaM <| inferArgumentTypesN matcherApp.alts.size matcherPartial
    let altNamesTypes := origAltTypes.mapIdx fun i ty => ((`alt).appendIndexAfter (i+1), ty)
    withLocalDeclsDND altNamesTypes fun alts => do
    -- Eta-expand fvar alts so `splitWith`/`matcherApp.transform` can `instantiateLambda` them.
    let abstractMatcherApp : MatcherApp := {
      matcherApp with
      matcherLevels := matcherLevels
      discrs        := discrs
      motive        := motive
      alts          := (← liftMetaM <| alts.mapM etaExpand)
      remaining     := #[]
    }
    k (.matcher abstractMatcherApp) (discrs ++ alts)

def splitWith
  {n} [MonadLiftT MetaM n] [MonadControlT MetaM n] [Monad n] [MonadError n] [MonadEnv n] [MonadLog n]
  [AddMessageContext n] [MonadOptions n]
  (info : SplitInfo) (resTy : Expr) (onAlt : Name → Expr → Nat → MatcherApp.TransformAltFVars → n Expr) (useSplitter := false) : n Expr := match info with
  | ite e => do
    let u ← getLevel resTy
    let c := e.getArg! 1
    let h := e.getArg! 2
    if useSplitter then -- dite is the "splitter" for ite
      let n ← liftMetaM <| mkFreshUserName `h
      let t ← withLocalDecl n .default c fun h => do mkLambdaFVars #[h] (← onAlt `isTrue resTy 0 { fields := #[h] })
      let e ← withLocalDecl n .default (mkNot c) fun h => do mkLambdaFVars #[h] (← onAlt `isFalse resTy 1 { fields := #[h] })
      return mkApp5 (mkConst ``_root_.dite [u]) resTy c h t e
    else
      let t ← onAlt `isTrue resTy 0 { fields := #[] }
      let e ← onAlt `isFalse resTy 1 { fields := #[] }
      return mkApp5 (mkConst ``_root_.ite [u]) resTy c h t e
  | dite e => do
    let u ← getLevel resTy
    let c := e.getArg! 1
    let h := e.getArg! 2
    let n ← liftMetaM <| mkFreshUserName `h
    let t ← withLocalDecl n .default c fun h => do mkLambdaFVars #[h] (← onAlt `isTrue resTy 0 { args := #[h], fields := #[h] })
    let e ← withLocalDecl n .default (mkNot c) fun h => do mkLambdaFVars #[h] (← onAlt `isFalse resTy 1 { args := #[h], fields := #[h] })
    return mkApp5 (mkConst ``_root_.dite [u]) resTy c h t e
  | matcher matcherApp => do
    let mask := matcherApp.discrs.map (·.isFVar)
    let maskedDiscrs := Array.mask mask matcherApp.discrs
    let absMotiveBody ← resTy.abstractM maskedDiscrs
    (·.toExpr) <$> matcherApp.transform
      (useSplitter := useSplitter) (addEqualities := useSplitter) -- (freshenNames := true)
      (onMotive := fun xs _body => pure (absMotiveBody.instantiateRev (Array.mask mask xs)))
      (onAlt := fun idx expAltType altFVars _alt => do
        onAlt ((`h).appendIndexAfter (idx+1)) expAltType idx altFVars)

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
    rwIfWith (mkFVar fv) e
  else
    rwMatcher idx e
