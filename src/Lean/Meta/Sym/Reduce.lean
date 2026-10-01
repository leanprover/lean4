/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.SymM
import Lean.Meta.Sym.InstantiateS
import Lean.Meta.Sym.AlphaShareBuilder
import Lean.Meta.WHNF
import Lean.ProjFns
namespace Lean.Meta.Sym
open Lean.Meta.Sym.Internal

/-!
# Definitional reduction steps

Single reduction steps on maximally shared terms, shared by `Sym.dsimp`, `Sym.simp`, and the
`grind` normalizer. Each function returns `none` when the step does not apply, and a maximally
shared term otherwise. The input and the output are definitionally equal.
-/

/-- Beta-reduces `e` when its head is a lambda. -/
public def reduceBeta? (e : Expr) : SymM (Option Expr) := do
  unless e.isApp do return none
  let f := e.getAppFn
  unless f.isHeadBetaTargetFn false do return none
  return some (← betaRevS f e.getAppRevArgs)

/-- Zeta-reduces the `let`/`have` telescope `e`: `let x := v; b[x]` becomes `b[v]`. -/
public def reduceZeta? (e : Expr) : SymM (Option Expr) := do
  let .letE .. := e | return none
  return some (← go e #[])
where
  go (e : Expr) (subst : Array Expr) : SymM Expr := do
    match e with
    | .letE _ _ v b _ => go b (subst.push (← instantiateRevS v subst))
    | _ => instantiateRevS e subst

/--
Unfolds the let-bound free variable at the head of `e`, where `e` is the variable itself or an
application headed by it. The head position must be handled by the caller because the
simplifiers do not visit application heads. Beta-reduction of the exposed lambda is left to
`reduceBeta?`.
-/
public def reduceZetaDelta? (e : Expr) (unfold : FVarId → Bool := fun _ => true) : SymM (Option Expr) := do
  let .fvar fvarId := e.getAppFn | return none
  unless unfold fvarId do return none
  let some value := (← fvarId.getDecl).value? | return none
  if e.isApp then
    return some (← mkAppNS value e.getAppArgs)
  else
    return some value

/--
Reduces a projection function applied to a constructor, e.g. `(a, b).1` to `a`.
Class projections are not reduced; instances are handled by instance synthesis.
-/
public def reduceProjApp? (e : Expr) : SymM (Option Expr) := do
  let .const declName _ := e.getAppFn | return none
  let some info ← getProjectionFnInfo? declName | return none
  if info.fromClass then return none
  let some e ← unfoldDefinition? e | return none
  let some f ← reduceProj? e.getAppFn | return none
  return some (← shareCommon (mkAppN f e.getAppArgs))

/-- Iota-reduces a `match` or recursor application whose discriminants are constructors. -/
public def reduceMatcherApp? (e : Expr) : SymM (Option Expr) := do
  let some e' ← reduceRecMatcher? e | return none
  -- Iota-reduction may expose kernel `Expr.proj` terms via struct-eta,
  -- which the structural simplifiers cannot consume directly.
  return some (← share (← foldProjs e'))

end Lean.Meta.Sym
