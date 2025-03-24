/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Grind.Util
import Lean.Util.PtrSet
import Lean.Meta.Basic
import Lean.Meta.InferType
import Lean.Meta.Tactic.Grind.Util

namespace Lean.Meta.Grind

unsafe def markNestedProofsImpl (e : Expr) : MetaM Expr := do
  visit e |>.run' mkPtrMap
where
  visit (e : Expr) : StateRefT (PtrMap Expr Expr) MetaM Expr := do
    if (← isProof e) then
      if e.isAppOf ``Lean.Grind.nestedProof then
        return e -- `e` is already marked
      if let some r := (← get).find? e then
        return r
      let prop ← inferType e
      /-
      We must unfold reducible constants occurring in `prop` because the congruence closure
      module in `grind` assumes they have been expanded.
      See `grind_mark_nested_proofs_bug.lean` for an example.
      TODO: We may have to normalize `prop` too.
      -/
      let prop ← unfoldReducible prop
      let e' := mkApp2 (mkConst ``Lean.Grind.nestedProof) prop e
      modify fun s => s.insert e e'
      return e'
    -- Remark: we have to process `Expr.proj` since we only
    -- fold projections later during term internalization
    unless e.isApp || e.isForall || e.isProj do
      return e
    -- Check whether it is cached
    if let some r := (← get).find? e then
      return r
    let e' ← match e with
      | .app .. => e.withApp fun f args => do
        let mut modified := false
        let mut args := args
        for i in [:args.size] do
          let arg := args[i]!
          let arg' ← visit arg
          unless ptrEq arg arg' do
            args := args.set! i arg'
            modified := true
        if modified then
          pure <| mkAppN f args
        else
          pure e
      | .proj _ _ b =>
        pure <| e.updateProj! (← visit b)
      | .forallE _ d b _ =>
        -- Recall that we have `ForallProp.lean`.
        let d' ← visit d
        let b' ← if b.hasLooseBVars then pure b else visit b
        pure <| e.updateForallE! d' b'
      | _ => unreachable!
    modify fun s => s.insert e e'
    return e'

/--
Wrap nested proofs `e` with `Lean.Grind.nestedProof`-applications.
Recall that the congruence closure module has special support for `Lean.Grind.nestedProof`.
-/
def markNestedProofs (e : Expr) : MetaM Expr :=
  unsafe markNestedProofsImpl e

end Lean.Meta.Grind
