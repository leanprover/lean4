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

public abbrev Result.isRfl : Result → Bool
  | .rfl false _ => true
  | _ => false

public def mkEqTrans (e₁ : Expr) (e₂ : Expr) (h₁ : Expr) (e₃ : Expr) (h₂ : Expr) : SymM Expr := do
  let α ← Sym.inferType e₁
  let u ← Sym.getLevel α
  return mkApp6 (mkConst ``Eq.trans [u]) α e₁ e₂ e₃ h₁ h₂

/-- Chains two simplification steps via `Eq.trans`.
`cd₁` is the `contextDependent` flag from the first step (whose proof is `h₁`).
The output is context-dependent if either step was: in another local context,
either step might produce a different result, changing the whole chain. -/
public abbrev mkEqTransResult (e₁ : Expr) (e₂ : Expr) (h₁ : Expr) (r₂ : Result)
    (cd₁ : Bool := false) : SymM Result :=
  match r₂ with
  | .rfl done cd₂ => return .step e₂ h₁ done (cd₁ || cd₂)
  | .step e₃ h₂ done cd₂ => return .step e₃ (← mkEqTrans e₁ e₂ h₁ e₃ h₂) done (cd₁ || cd₂)

public def Result.markAsDone : Result → Result
  | .rfl _ cd => .rfl true cd
  | .step e h _ cd => .step e h true cd

public def Result.getResultExpr : Expr → Result → Expr
  | e, .rfl _ _ => e
  | _, .step e _ _ _ => e

end Lean.Meta.Sym.Simp
