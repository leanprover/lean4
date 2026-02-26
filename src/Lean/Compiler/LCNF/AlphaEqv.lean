/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Compiler.LCNF.Basic
import Init.Omega

public section

namespace Lean.Compiler.LCNF

/-!
Alpha equivalence for LCNF Code
-/

namespace AlphaEqv

abbrev EqvM := ReaderM (FVarIdMap FVarId)

def eqvFVar (fvarId₁ fvarId₂ : FVarId) : EqvM Bool := do
  let fvarId₂ := (← read).get? fvarId₂ |>.getD fvarId₂
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

def eqvArg (a₁ a₂ : Arg pu) : EqvM Bool := do
  match a₁, a₂ with
  | .type e₁ _, .type e₂ _ => eqvType e₁ e₂
  | .fvar x₁, .fvar x₂ => eqvFVar x₁ x₂
  | .erased, .erased => return true
  | _, _ => return false

def eqvArgs (as₁ as₂ : Array (Arg pu)) : EqvM Bool := do
  if as₁.size = as₂.size then
    for a₁ in as₁, a₂ in as₂ do
      unless (← eqvArg a₁ a₂) do
        return false
    return true
  else
    return false

def eqvLetValue (e₁ e₂ : LetValue pu) : EqvM Bool := do
  match e₁, e₂ with
  | .lit v₁, .lit v₂ => return v₁ == v₂
  | .erased, .erased => return true
  | .proj s₁ i₁ x₁ _, .proj s₂ i₂ x₂ _ => pure (s₁ == s₂ && i₁ == i₂) <&&> eqvFVar x₁ x₂
  | .const n₁ us₁ as₁ _, .const n₂ us₂ as₂ _ => pure (n₁ == n₂ && us₁ == us₂) <&&> eqvArgs as₁ as₂
  | .fvar f₁ as₁, .fvar f₂ as₂ => eqvFVar f₁ f₂ <&&> eqvArgs as₁ as₂
  | .ctor i₁ as₁ _, .ctor i₂ as₂ _ => pure (i₁ == i₂) <&&> eqvArgs as₁ as₂
  | .oproj i₁ v₁ _, .oproj i₂ v₂ _ => pure (i₁ == i₂) <&&> eqvFVar v₁ v₂
  | .uproj i₁ v₁ _, .uproj i₂ v₂ _ => pure (i₁ == i₂) <&&> eqvFVar v₁ v₂
  | .sproj i₁ o₁ v₁ _, .sproj i₂ o₂ v₂ _ => pure (i₁ == i₂ && o₁ == o₂) <&&> eqvFVar v₁ v₂
  | .fap f₁ as₁ _, .fap f₂ as₂ _ => pure (f₁ == f₂) <&&> eqvArgs as₁ as₂
  | .pap f₁ as₁ _, .pap f₂ as₂ _ => pure (f₁ == f₂) <&&> eqvArgs as₁ as₂
  | .reset n₁ v₁ _, .reset n₂ v₂ _ => pure (n₁ == n₂) <&&> eqvFVar v₁ v₂
  | .reuse v₁ i₁ u₁ as₁ _, .reuse v₂ i₂ u₂ as₂ _ =>
    pure (i₁ == i₂ && u₁ == u₂) <&&> eqvFVar v₁ v₂ <&&> eqvArgs as₁ as₂
  | .box ty₁ v₁ _, .box ty₂ v₂ _ => eqvType ty₁ ty₂ <&&> eqvFVar v₁ v₂
  | .unbox v₁ _, .unbox v₂ _ => eqvFVar v₁ v₂
  | .isShared v₁ _, .isShared v₂ _ => eqvFVar v₁ v₂
  | _, _ => return false

@[inline] def withFVar (fvarId₁ fvarId₂ : FVarId) (x : EqvM α) : EqvM α :=
  withReader (·.insert fvarId₂ fvarId₁) x

@[inline] def withParams (params₁ params₂ : Array (Param pu)) (x : EqvM Bool) : EqvM Bool := do
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

def sortAlts (alts : Array (Alt pu)) : Array (Alt pu) :=
  alts.qsort fun
    | .alt .., .default .. => true
    | .ctorAlt .., .default .. => true
    | .alt ctorName₁ .., .alt ctorName₂ .. => Name.lt ctorName₁ ctorName₂
    | .ctorAlt i₁ .., .ctorAlt i₂ .. => Name.lt i₁.name i₂.name
    | _, _  => false

mutual

partial def eqvAlts (alts₁ alts₂ : Array (Alt pu)) : EqvM Bool := do
  if alts₁.size = alts₂.size then
    let alts₁ := sortAlts alts₁
    let alts₂ := sortAlts alts₂
    for alt₁ in alts₁, alt₂ in alts₂ do
      match alt₁, alt₂ with
      | .alt ctorName₁ ps₁ k₁ _, .alt ctorName₂ ps₂ k₂ _ =>
        unless ctorName₁ == ctorName₂ do return false
        unless (← withParams ps₁ ps₂ (eqv k₁ k₂)) do return false
      | .ctorAlt i₁ k₁ _, .ctorAlt i₂ k₂ _ =>
        unless i₁ == i₂ do return false
        unless ← eqv k₁ k₂ do return false
      | .default k₁, .default k₂ => unless (← eqv k₁ k₂) do return false
      | _, _ => return false
    return true
  else
    return false

partial def eqv (code₁ code₂ : Code pu) : EqvM Bool := do
  match code₁, code₂ with
  | .let decl₁ k₁, .let decl₂ k₂ =>
    eqvType decl₁.type decl₂.type <&&>
    eqvLetValue decl₁.value decl₂.value <&&>
    withFVar decl₁.fvarId decl₂.fvarId (eqv k₁ k₂)
  | .fun decl₁ k₁ _, .fun decl₂ k₂ _
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
  | .oset fvarId₁ i₁ y₁ k₁ _, .oset fvarId₂ i₂ y₂ k₂ _ =>
    pure (i₁ == i₂) <&&>
    eqvFVar fvarId₁ fvarId₂ <&&>
    eqvArg y₁ y₂ <&&>
    eqv k₁ k₂
  | .sset fvarId₁ i₁ offset₁ y₁ ty₁ k₁ _, .sset fvarId₂ i₂ offset₂ y₂ ty₂ k₂ _ =>
    pure (i₁ == i₂) <&&>
    pure (offset₁ == offset₂) <&&>
    eqvFVar fvarId₁ fvarId₂ <&&>
    eqvFVar y₁ y₂ <&&>
    eqvType ty₁ ty₂ <&&>
    eqv k₁ k₂
  | .uset fvarId₁ i₁ y₁ k₁ _, .uset fvarId₂ i₂ y₂ k₂ _ =>
    pure (i₁ == i₂) <&&>
    eqvFVar fvarId₁ fvarId₂ <&&>
    eqvFVar y₁ y₂ <&&>
    eqv k₁ k₂
  | .setTag fvarId₁ c₁ k₁ _, .setTag fvarId₂ c₂ k₂ _ =>
    pure (c₁ == c₂) <&&>
    eqvFVar fvarId₁ fvarId₂ <&&>
    eqv k₁ k₂
  | .inc fvarId₁ n₁ c₁ p₁ k₁ _, .inc fvarId₂ n₂ c₂ p₂ k₂ _ =>
    pure (n₁ == n₂) <&&>
    pure (c₁ == c₂) <&&>
    pure (p₁ == p₂) <&&>
    eqvFVar fvarId₁ fvarId₂ <&&>
    eqv k₁ k₂
  | .dec fvarId₁ n₁ c₁ p₁ k₁ _, .dec fvarId₂ n₂ c₂ p₂ k₂ _ =>
    pure (n₁ == n₂) <&&>
    pure (c₁ == c₂) <&&>
    pure (p₁ == p₂) <&&>
    eqvFVar fvarId₁ fvarId₂ <&&>
    eqv k₁ k₂
  | .del fvarId₁ k₁ _, .del fvarId₂ k₂ _ =>
    eqvFVar fvarId₁ fvarId₂ <&&>
    eqv k₁ k₂
  | _, _ => return false

end

end AlphaEqv

/--
Return `true` if `c₁` and `c₂` are alpha equivalent.
-/
def Code.alphaEqv (c₁ c₂ : Code pu) : Bool :=
  AlphaEqv.eqv c₁ c₂ |>.run {}

end Lean.Compiler.LCNF
