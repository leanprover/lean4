/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
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

def eqvType (e₁ e₂ : Expr) : EqvM Bool := do
  match e₁, e₂ with
  | .app f₁ a₁, .app f₂ a₂ => eqvType a₁ a₂ <&&> eqvType f₁ f₂
  | .fvar fvarId₁, .fvar fvarId₂ => eqvFVar fvarId₁ fvarId₂
  | .forallE _ d₁ b₁ _, .forallE _ d₂ b₂ _ => eqvType d₁ d₂ <&&> eqvType b₁ b₂
  | _, _ => return e₁ == e₂

def eqvTypes (es₁ es₂ : Array Expr) : EqvM Bool := do
  if es₁.size = es₂.size then
    for e₁ in es₁, e₂ in es₂ do
      unless (← eqvType e₁ e₂) do
        return false
    return true
  else
    return false

def eqvArg (a₁ a₂ : Arg) : EqvM Bool := do
  match a₁, a₂ with
  | .type e₁, .type e₂ => eqvType e₁ e₂
  | .fvar x₁, .fvar x₂ => eqvFVar x₁ x₂
  | .erased, .erased => return true
  | _, _ => return false

def eqvArgs (as₁ as₂ : Array Arg) : EqvM Bool := do
  if as₁.size = as₂.size then
    for a₁ in as₁, a₂ in as₂ do
      unless (← eqvArg a₁ a₂) do
        return false
    return true
  else
    return false

def eqvLetValue (e₁ e₂ : LetValue) : EqvM Bool := do
  match e₁, e₂ with
  | .value v₁, .value v₂ => return v₁ == v₂
  | .erased, .erased => return true
  | .proj s₁ i₁ x₁, .proj s₂ i₂ x₂ => pure (s₁ == s₂ && i₁ == i₂) <&&> eqvFVar x₁ x₂
  | .const n₁ us₁ as₁, .const n₂ us₂ as₂ => pure (n₁ == n₂ && us₁ == us₂) <&&> eqvArgs as₁ as₂
  | .fvar f₁ as₁, .fvar f₂ as₂ => eqvFVar f₁ f₂ <&&> eqvArgs as₁ as₂
  | _, _ => return false

@[inline] def withFVar (fvarId₁ fvarId₂ : FVarId) (x : EqvM α) : EqvM α :=
  withReader (·.insert fvarId₂ fvarId₁) x

@[inline] def withParams (params₁ params₂ : Array Param) (x : EqvM Bool) : EqvM Bool := do
  if h : params₂.size = params₁.size then
    let rec @[specialize] go (i : Nat) : EqvM Bool := do
      if h : i < params₁.size then
        let p₁ := params₁[i]
        have : i < params₂.size := by simp_all +arith
        let p₂ := params₂[i]
        unless (← eqvType p₁.type p₂.type) do return false
        withFVar p₁.fvarId p₂.fvarId do
          go (i+1)
      else
        x
      termination_by params₁.size - i
    go 0
  else
    return false

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
    eqvType decl₁.type decl₂.type <&&>
    eqvLetValue decl₁.value decl₂.value <&&>
    withFVar decl₁.fvarId decl₂.fvarId (eqv k₁ k₂)
  | .fun decl₁ k₁, .fun decl₂ k₂
  | .jp decl₁ k₁, .jp decl₂ k₂ =>
    eqvType decl₁.type decl₂.type <&&>
    withParams decl₁.params decl₂.params (eqv decl₁.value decl₂.value) <&&>
    withFVar decl₁.fvarId decl₂.fvarId (eqv k₁ k₂)
  | .return fvarId₁, .return fvarId₂ => eqvFVar fvarId₁ fvarId₂
  | .unreach type₁, .unreach type₂ => eqvType type₁ type₂
  | .jmp fvarId₁ args₁, .jmp fvarId₂ args₂ => eqvFVar fvarId₁ fvarId₂ <&&> eqvArgs args₁ args₂
  | .cases c₁, .cases c₂ =>
    eqvFVar c₁.discr c₂.discr <&&>
    eqvType c₁.resultType c₂.resultType <&&>
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
