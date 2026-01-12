/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.Simp.SimpM
public import Lean.Meta.Sym.InferType
namespace Lean.Meta.Sym.Simp

public abbrev Result.isRfl (result : Result) : Bool :=
  result matches .rfl

public def mkEqTrans (e₁ : Expr) (e₂ : Expr) (h₁ : Expr) (e₃ : Expr) (h₂ : Expr) : SymM Expr := do
  let α ← Sym.inferType e₁
  let u ← Sym.getLevel α
  return mkApp6 (mkConst ``Eq.trans [u]) α e₁ e₂ e₃ h₁ h₂

public abbrev mkEqTransResult (e₁ : Expr) (e₂ : Expr) (h₁ : Expr) (r₂ : Result) : SymM Result :=
  match r₂ with
  | .rfl done => return .step e₂ h₁ done
  | .step e₃ h₂ done => return .step e₃ (← mkEqTrans e₁ e₂ h₁ e₃ h₂) done

end Lean.Meta.Sym.Simp
