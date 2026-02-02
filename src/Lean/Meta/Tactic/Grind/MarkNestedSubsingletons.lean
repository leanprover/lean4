/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Types
import Init.Grind.Util
import Lean.Meta.Sym.ExprPtr
import Lean.Meta.Sym.Util
import Lean.Meta.Tactic.Grind.Util
public section
namespace Lean.Meta.Grind

private abbrev M := StateRefT (Std.HashMap ExprPtr Expr) GrindM

def isMarkedSubsingletonConst (e : Expr) : Bool := Id.run do
  let .const declName _ := e | false
  return declName == ``Grind.nestedProof || declName == ``Grind.nestedDecidable

def isMarkedSubsingletonApp (e : Expr) : Bool :=
  /-
  Remark: we must check `e`s arity because we may have over-applied `Grind.nestedProof` applications.
  These over-applied applications have to be re-marked. Here is an example from test `grind_over_applied_nestedProof.lean`
  ```
  ‹∀ (a : Option α), x = some a → ∀ (a_2 : α), a = some a_2 → p a_2› val (join_pmap_eq_pmap_join._proof_1_2 val h_1))
  ```
  -/
  isMarkedSubsingletonConst e.getAppFn && e.getAppNumArgs == 2

/-- Returns `some p` if `e` is of the form `Decidable p` -/
private def isDecidable (e : Expr) : MetaM (Option Expr) := do
  match_expr (← whnfCore e) with
  | Decidable p => return some p
  | _ => return none

/--
Wrap nested proofs and decidable instances in `e` with `Lean.Grind.nestedProof` and `Lean.Grind.nestedDecidable`-applications.
Recall that the congruence closure module has special support for them.
-/
-- TODO: consider other subsingletons in the future? We decided to not support them to avoid the overhead of
-- synthesizing `Subsingleton` instances.
partial def markNestedSubsingletons (e : Expr) : GrindM Expr := do profileitM Exception "grind mark subsingleton" (← getOptions) do
  visit e |>.run' {}
where
  visit (e : Expr) : M Expr := do
    if isMarkedSubsingletonApp e then
      return e -- `e` is already marked
    -- check whether result is cached
    if let some r := (← get).get? { expr := e } then
      return r
    -- check whether `e` is a proposition or `Decidable`
    let type ← inferType e
    if (← isProp type) then
      let e' := mkApp2 (mkConst ``Grind.nestedProof) (← preprocess type) e
      modify fun s => s.insert { expr := e } e'
      return e'
    if let some p ← isDecidable type then
      let e' := mkApp2 (mkConst ``Grind.nestedDecidable) (← preprocess p) e
      modify fun s => s.insert { expr := e } e'
      return e'
    -- Remark: we have to process `Expr.proj` since we only
    -- fold projections later during term internalization
    unless e.isApp || e.isForall || e.isProj || e.isMData do
      return e
    let e' ← match e with
      | .app .. => e.withApp fun f args => do
        let mut modified := false
        let mut args := args.toVector
        for h : i in *...args.size do
          let arg := args[i]
          let arg' ← visit arg
          unless isSameExpr arg arg' do
            args := args.set i arg'
            modified := true
        if modified then
          pure <| mkAppN f args.toArray
        else
          pure e
      | .proj _ _ b =>
        pure <| e.updateProj! (← visit b)
      | .mdata _ b =>
        pure <| e.updateMData! (← visit b)
      | .forallE _ d b _ =>
        -- Recall that we have `ForallProp.lean`.
        let d' ← visit d
        let b' ← if b.hasLooseBVars then pure b else visit b
        pure <| e.updateForallE! d' b'
      | _ => unreachable!
    modify fun s => s.insert { expr := e } e'
    return e'

  preprocess (e : Expr) : M Expr := do
    /-
    **Note**: We must use `instantiateMVars` here because this function is called using the result of `inferType`.
    -/
    let e ← instantiateMVars e
    /-
    We must unfold reducible constants occurring in `prop` because the congruence closure
    module in `grind` assumes they have been expanded.
    See `grind_mark_nested_proofs_bug.lean` for an example.
    TODO: We may have to normalize `prop` too.
    -/
    /- We must also apply beta-reduction to improve the effectiveness of the congruence closure procedure. -/
    let e ← Core.betaReduce e
    let e ← Sym.unfoldReducible e
    /- We must mask proofs occurring in `prop` too. -/
    let e ← visit e
    let e ← eraseIrrelevantMData e
    /- We must fold kernel projections like it is done in the preprocessor. -/
    let e ← foldProjs e
    normalizeLevels e

private def markNestedProof (e : Expr) : M Expr := do
  let prop ← inferType e
  let prop ← markNestedSubsingletons.preprocess prop
  return mkApp2 (mkConst ``Grind.nestedProof) prop e

/--
Given a proof `e`, mark it with `Lean.Grind.nestedProof`
-/
def markProof (e : Expr) : GrindM Expr := do
  if e.isAppOf ``Grind.nestedProof then
    return e -- `e` is already marked
  else
    markNestedProof e |>.run' {}

end Lean.Meta.Grind
