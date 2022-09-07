/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.LCNF.Basic

namespace Lean.Compiler.LCNF

/-!
Alpha equivalence for LCNF Code
-/

namespace AlphaEqv

abbrev EqvM := ReaderM (FVarIdMap FVarId)

def eqvFVar (fvarId₁ fvarId₂ : FVarId) : EqvM Bool := do
  let fvarId₂ := (← read).find? fvarId₂ |>.getD fvarId₂
  return fvarId₁ == fvarId₂

def eqvExpr (e₁ e₂ : Expr) : EqvM Bool := do
  match e₁, e₂ with
  | .app f₁ a₁, .app f₂ a₂ => eqvExpr a₁ a₂ <&&> eqvExpr f₁ f₂
  | .proj s₁ i₁ e₁, .proj s₂ i₂ e₂ => pure (s₁ == s₂ && i₁ == i₂) <&&> eqvExpr e₁ e₂
  | .mdata m₁ e₁, .mdata m₂ e₂ => pure (m₁ == m₂) <&&> eqvExpr e₁ e₂
  | .fvar fvarId₁, .fvar fvarId₂ => eqvFVar fvarId₁ fvarId₂
  | .forallE _ d₁ b₁ _, .forallE _ d₂ b₂ _ => eqvExpr d₁ d₂ <&&> eqvExpr b₁ b₂
  | .letE .., _ | _, .letE .. => unreachable!
  | _, _ => return e₁ == e₂

def eqvExprs (es₁ es₂ : Array Expr) : EqvM Bool := do
  if es₁.size = es₂.size then
    for e₁ in es₁, e₂ in es₂ do
      unless (← eqvExpr e₁ e₂) do
        return false
    return true
  else
    return false

@[inline] def withFVar (fvarId₁ fvarId₂ : FVarId) (x : EqvM α) : EqvM α :=
  withReader (·.insert fvarId₂ fvarId₁) x

@[inline] def withParams (params₁ params₂ : Array Param) (x : EqvM Bool) : EqvM Bool := do
  if h : params₂.size = params₁.size then
    let rec @[specialize] go (i : Nat) : EqvM Bool := do
      if h : i < params₁.size then
        let p₁ := params₁[i]
        have : i < params₂.size := by simp_all_arith
        let p₂ := params₂[i]
        unless (← eqvExpr p₁.type p₂.type) do return false
        withFVar p₁.fvarId p₂.fvarId do
          go (i+1)
      else
        x
    go 0
  else
    return false
termination_by go i => params₁.size - i

def sortAlts (alts : Array Alt) : Array Alt :=
  alts.qsort fun
    | .alt .., .default .. => true
    | .alt ctorName₁ .., .alt ctorName₂ .. => Name.lt ctorName₁ ctorName₂
    | _, _  => false

mutual

partial def eqvAlts (alts₁ alts₂ : Array Alt) : EqvM Bool := do
  if alts₁.size = alts₂.size then
    let alts₁ := sortAlts alts₁
    let alts₂ := sortAlts alts₂
    for alt₁ in alts₁, alt₂ in alts₂ do
      match alt₁, alt₂ with
      | .alt ctorName₁ ps₁ k₁, .alt ctorName₂ ps₂ k₂ =>
        unless ctorName₁ == ctorName₂ do return false
        unless (← withParams ps₁ ps₂ (eqv k₁ k₂)) do return false
      | .default k₁, .default k₂ => unless (← eqv k₁ k₂) do return false
      | _, _ => return false
    return true
  else
    return false

partial def eqv (code₁ code₂ : Code) : EqvM Bool := do
  match code₁, code₂ with
  | .let decl₁ k₁, .let decl₂ k₂ =>
    eqvExpr decl₁.type decl₂.type <&&>
    eqvExpr decl₁.value decl₂.value <&&>
    withFVar decl₁.fvarId decl₂.fvarId (eqv k₁ k₂)
  | .fun decl₁ k₁, .fun decl₂ k₂
  | .jp decl₁ k₁, .jp decl₂ k₂ =>
    eqvExpr decl₁.type decl₂.type <&&>
    withParams decl₁.params decl₂.params (eqv decl₁.value decl₂.value) <&&>
    withFVar decl₁.fvarId decl₂.fvarId (eqv k₁ k₂)
  | .return fvarId₁, .return fvarId₂ => eqvFVar fvarId₁ fvarId₂
  | .unreach type₁, .unreach type₂ => eqvExpr type₁ type₂
  | .jmp fvarId₁ args₁, .jmp fvarId₂ args₂ => eqvFVar fvarId₁ fvarId₂ <&&> eqvExprs args₁ args₂
  | .cases c₁, .cases c₂ =>
    eqvFVar c₁.discr c₂.discr <&&>
    eqvExpr c₁.resultType c₂.resultType <&&>
    eqvAlts c₁.alts c₂.alts
  | _, _ => return false

end

end AlphaEqv

/--
Return `true` if `c₁` and `c₂` are alpha equivalent.
-/
def Code.alphaEqv (c₁ c₂ : Code) : Bool :=
  AlphaEqv.eqv c₁ c₂ |>.run {}

end Lean.Compiler.LCNF