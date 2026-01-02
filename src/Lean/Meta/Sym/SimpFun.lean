/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.SimpM
import Lean.Meta.Sym.EqTrans
namespace Lean.Meta.Sym.Simp

public def mkEqTrans (e : Expr) (r₁ : Result) (r₂ : Result) : SimpM Result := do
  let proof? ← Sym.mkEqTrans e r₁.expr r₁.proof? r₂.expr r₂.proof?
  return { r₂ with proof? }

public abbrev SimpFun := Expr → SimpM Result

public abbrev SimpFun.andThen (f g : SimpFun) : SimpFun := fun e => do
  let r₁ ← f e
  let r₂ ← g r₁.expr
  mkEqTrans e r₁ r₂

public instance : AndThen SimpFun where
  andThen f g := SimpFun.andThen f (g ())

end Lean.Meta.Sym.Simp
