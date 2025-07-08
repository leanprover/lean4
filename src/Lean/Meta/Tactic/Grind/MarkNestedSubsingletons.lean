/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Grind.Util
import Lean.Util.PtrSet
import Lean.Meta.Transform
import Lean.Meta.Basic
import Lean.Meta.InferType
import Lean.Meta.Tactic.Grind.ExprPtr
import Lean.Meta.Tactic.Grind.Util

namespace Lean.Meta.Grind

private abbrev M := StateRefT (Std.HashMap ExprPtr Expr) MetaM

/--
Wrap nested proofs and decidable instances in `e` with `Lean.Grind.nestedProof` and `Lean.Grind.nestedDecidable`-applications.
Recall that the congruence closure module has special support for them.
-/
-- TODO: consider other subsingletons in the future? We decided to not support them to avoid the overhead of
-- synthesizing `Subsingleton` instances.
partial def markNestedSubsingletons (e : Expr) : MetaM Expr := do
  visit e |>.run' {}
where
  visit (e : Expr) : M Expr := do
    if (← isProof e) then
      if e.isAppOf ``Lean.Grind.nestedProof then
        return e -- `e` is already marked
      if let some r := (← get).get? { expr := e } then
        return r
      let e' ← markNestedProof e
      modify fun s => s.insert { expr := e } e'
      return e'
    -- Remark: we have to process `Expr.proj` since we only
    -- fold projections later during term internalization
    unless e.isApp || e.isForall || e.isProj || e.isMData do
      return e
    -- Check whether it is cached
    if let some r := (← get).get? { expr := e } then
      return r
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
    We must unfold reducible constants occurring in `prop` because the congruence closure
    module in `grind` assumes they have been expanded.
    See `grind_mark_nested_proofs_bug.lean` for an example.
    TODO: We may have to normalize `prop` too.
    -/
    /- We must also apply beta-reduction to improve the effectiveness of the congruence closure procedure. -/
    let e ← Core.betaReduce e
    let e ← unfoldReducible e
    /- We must mask proofs occurring in `prop` too. -/
    let e ← visit e
    let e ← eraseIrrelevantMData e
    /- We must fold kernel projections like it is done in the preprocessor. -/
    let e ← foldProjs e
    normalizeLevels e

  markNestedProof (e : Expr) : M Expr := do
    let prop ← inferType e
    let prop ← preprocess prop
    return mkApp2 (mkConst ``Lean.Grind.nestedProof) prop e

/--
Given a proof `e`, mark it with `Lean.Grind.nestedProof`
-/
def markProof (e : Expr) : MetaM Expr := do
  if e.isAppOf ``Lean.Grind.nestedProof then
    return e -- `e` is already marked
  else
    unsafe markNestedSubsingletons.markNestedProof e |>.run' {}

end Lean.Meta.Grind
