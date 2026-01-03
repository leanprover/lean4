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
open Grind
public def mkEqTrans (e : Expr) (r₁ : Result) (r₂ : Result) : SimpM Result := do
  let proof? ← Sym.mkEqTrans e r₁.expr r₁.proof? r₂.expr r₂.proof?
  return { r₂ with proof? }

public abbrev Simproc.andThen (f g : Simproc) : Simproc := fun e => do
  let r₁ ← f e
  if isSameExpr e r₁.expr then
    g e
  else
    let r₂ ← g r₁.expr
    mkEqTrans e r₁ r₂

public instance : AndThen Simproc where
  andThen f g := Simproc.andThen f (g ())

end Lean.Meta.Sym.Simp
