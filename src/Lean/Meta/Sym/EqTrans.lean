/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.SimpM
import Lean.Meta.Sym.InferType
namespace Lean.Meta.Sym

public def mkEqTrans (e₁ : Expr) (e₂ : Expr) (h₁? : Option Expr) (e₃ : Expr) (h₂? : Option Expr) : SymM (Option Expr) := do
  match h₁?, h₂? with
  | none,    none    => return none
  | some _,  none    => return h₁?
  | none,    some _  => return h₂?
  | some h₁, some h₂ =>
    let α ← inferType e₁
    let u ← getLevel α
    return mkApp6 (mkConst ``Eq.trans [u]) α e₁ e₂ e₃ h₁ h₂

end Lean.Meta.Sym
