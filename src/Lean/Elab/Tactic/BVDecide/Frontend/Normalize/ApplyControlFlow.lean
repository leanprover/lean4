/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Lean.Meta.Tactic.Simp

/-!
This modules contains simprocs and functions to compute discrimination tree keys in order to
construct simp sets that apply `apply_ite` and `Bool.apply_cond` to specific functions.
-/

namespace Lean.Elab.Tactic.BVDecide
namespace Frontend.Normalize

open Lean.Meta

def applyIteSimproc : Simp.Simproc := fun e => e.withApp fun fn args => do
  if h : args.size ≠ 0 then
    let_expr ite α c instDec t e := args.back | return .continue
    let params := args.pop
    let fnApp := mkAppN fn params
    let newT := mkApp fnApp t
    let newE := mkApp fnApp e
    let newIf ← mkAppOptM ``ite #[none, c, instDec, newT, newE]
    let proof ← mkAppOptM ``apply_ite #[α, none, fnApp, c, instDec, t, e]
    return .visit { expr := newIf, proof? := some proof }
  else
    return .continue

def applyCondSimproc : Simp.Simproc := fun e => e.withApp fun fn args => do
  if h : args.size ≠ 0 then
    let_expr cond α c t e := args.back | return .continue
    let params := args.pop
    let fnApp := mkAppN fn params
    let newT := mkApp fnApp t
    let newE := mkApp fnApp e
    let newCond ← mkAppOptM ``cond #[none, c, newT, newE]
    let proof ← mkAppOptM ``Bool.apply_cond #[α, none, fnApp, c, t, e]
    return .visit { expr := newCond, proof? := some proof }
  else
    return .continue

/--
For `Prod.fst` and `ite` this function creates the path: `Prod.fst (ite (Prod _ _) _ _ _ _)`.
This path can be used to match on applications of structure projections onto control flow primitives.
-/
def mkApplyProjControlDiscrPath (struct : Name) (structParams : Nat) (projIdx : Nat)
    (controlFlow : Name) (controlFlowParams : Nat) : Array DiscrTree.Key := Id.run do
  let stars := structParams + controlFlowParams - 1
  let mut path : Array DiscrTree.Key := Array.mkEmpty (3 + stars)
  path := path.push <| .proj struct projIdx 0
  path := path.push <| .const controlFlow controlFlowParams
  path := path.push <| .const struct structParams
  path := Nat.fold (init := path) stars (fun _ _ acc => acc.push .star)
  return path

/--
For `f`, `SomeType α β` and `ite` this function creates the path: `f (ite (SomeType _ _) _ _ _ _)`.
This path can be used to match on applications of unary functions onto control flow primitives.
-/
def mkApplyUnaryControlDiscrPath (type : Name) (typeParams : Nat) (constName : Name)
    (controlFlow : Name) (controlFlowParams : Nat) : Array DiscrTree.Key := Id.run do
  let stars := typeParams + controlFlowParams - 1
  let mut path : Array DiscrTree.Key := Array.mkEmpty (3 + stars)
  path := path.push <| .const constName 1
  path := path.push <| .const controlFlow controlFlowParams
  path := path.push <| .const type typeParams
  path := Nat.fold (init := path) stars (fun _ _ acc => acc.push .star)
  return path


end Frontend.Normalize
end Lean.Elab.Tactic.BVDecide
