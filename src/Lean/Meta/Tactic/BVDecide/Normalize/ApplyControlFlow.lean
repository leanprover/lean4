/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean.Meta.Tactic.Simp
import Init.ByCases
import Init.Omega
public import Lean.Meta.Sym.Simp.SimpM

/-!
This modules contains simprocs and functions to compute discrimination tree keys in order to
construct simp sets that apply `apply_ite` and `Bool.apply_cond` to specific functions.
-/

namespace Lean.Meta.Tactic.BVDecide
namespace Normalize

public def applyIteSimproc (headSyms : Std.HashSet Name) :
    Sym.Simp.Simproc := fun e => e.withApp fun fn args => do
  if h : args.size ≠ 0 then
    let_expr ite α c instDec t e := args.back | return .rfl
    let .const head _ := fn | return .rfl
    unless headSyms.contains head do return .rfl
    let params := args.pop
    let fnApp := mkAppN fn params
    let newT := mkApp fnApp t
    let newE := mkApp fnApp e
    let newIf ← Sym.share <| ← mkAppOptM ``ite #[none, c, instDec, newT, newE]
    let proof ← mkAppOptM ``apply_ite #[α, none, fnApp, c, instDec, t, e]
    return .step newIf proof
  else
    return .rfl

public def applyCondSimproc (headSyms : Std.HashSet Name) :
    Sym.Simp.Simproc := fun e => e.withApp fun fn args => do
  if h : args.size ≠ 0 then
    let_expr cond α c t e := args.back | return .rfl
    let .const head _ := fn | return .rfl
    unless headSyms.contains head do return .rfl
    let params := args.pop
    let fnApp := mkAppN fn params
    let newT := mkApp fnApp t
    let newE := mkApp fnApp e
    let newCond ← Sym.share <| ← mkAppOptM ``cond #[none, c, newT, newE]
    let proof ← mkAppOptM ``Bool.apply_cond #[α, none, fnApp, c, t, e]
    return .step newCond proof
  else
    return .rfl

end Normalize
end Lean.Meta.Tactic.BVDecide
