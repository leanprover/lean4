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
      let e' := mkApp2 (mkConst ``Lean.Grind.nestedProof) prop e
      modify fun s => s.insert e e'
      return e'
    else match e with
      | .bvar .. => unreachable!
      -- See comments on `Canon.lean` for why we do not visit these cases.
      | .letE .. | .forallE .. | .lam ..
      | .const .. | .lit .. | .mvar .. | .sort .. | .fvar ..
      | .proj ..
      | .mdata ..  => return e
      -- We only visit applications
      | .app .. =>
        -- Check whether it is cached
        if let some r := (← get).find? e then
          return r
        e.withApp fun f args => do
          let mut modified := false
          let mut args := args
          for i in [:args.size] do
            let arg := args[i]!
            let arg' ← visit arg
            unless ptrEq arg arg' do
              args := args.set! i arg'
              modified := true
          let e' := if modified then mkAppN f args else e
          modify fun s => s.insert e e'
          return e'

/--
Wrap nested proofs `e` with `Lean.Grind.nestedProof`-applications.
Recall that the congruence closure module has special support for `Lean.Grind.nestedProof`.
-/
def markNestedProofs (e : Expr) : MetaM Expr :=
  unsafe markNestedProofsImpl e

end Lean.Meta.Grind
