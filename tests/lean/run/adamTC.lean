inductive Expr where
  | nat  : Nat → Expr
  | plus : Expr → Expr → Expr
  | bool : Bool → Expr
  | and  : Expr → Expr → Expr
  deriving DecidableEq

inductive Ty where
  | nat
  | bool
  deriving DecidableEq

inductive HasType : Expr → Ty → Prop
  | nat  : HasType (.nat v) .nat
  | plus : HasType a .nat → HasType b .nat → HasType (.plus a b) .nat
  | bool : HasType (.bool v) .bool
  | and  : HasType a .bool → HasType b .bool → HasType (.and a b) .bool

def Expr.typeCheck (e : Expr) : Option {t : Ty // HasType e t} :=
  match e with
  | nat ..   => some ⟨.nat, .nat⟩
  | bool ..  => some ⟨.bool, .bool⟩
  | plus a b =>
    match a.typeCheck, b.typeCheck with
    | some ⟨.nat, h₁⟩, some ⟨.nat, h₂⟩ => some ⟨.nat, .plus h₁ h₂⟩
    | _, _ => none
  | and a b =>
    match a.typeCheck, b.typeCheck with
    | some ⟨.bool, h₁⟩, some ⟨.bool, h₂⟩ => some ⟨.bool, .and h₁ h₂⟩
    | _, _ => none

theorem HasType.det (h₁ : HasType e t₁) (h₂ : HasType e t₂) : t₁ = t₂ := by
  cases h₁ <;> cases h₂ <;> rfl

-- TODO: for simplifying the following proof we need: ematching for forward reasoning, and `match` blast for case analysis

theorem Expr.typeCheck_complete {e : Expr} : e.typeCheck = none → ¬ HasType e t := by
  induction e with simp [typeCheck]
  | plus a b iha ihb =>
    revert iha ihb
    cases typeCheck a <;> cases typeCheck b <;> simp <;> intros <;> intro h <;> cases h <;> try contradiction
    rename_i r₁ r₂ h _ _
    cases r₁; rename_i t₁ _; cases r₂; rename_i t₂ _; cases t₁ <;> cases t₂ <;> simp at h
    . have := HasType.det ‹HasType b Ty.bool› ‹HasType b Ty.nat›; contradiction
    . have := HasType.det ‹HasType a Ty.bool› ‹HasType a Ty.nat›; contradiction
    . have := HasType.det ‹HasType a Ty.bool› ‹HasType a Ty.nat›; contradiction
  | and a b iha ihb =>
    revert iha ihb
    cases typeCheck a <;> cases typeCheck b <;> simp <;> intros <;> intro h <;> cases h <;> try contradiction
    rename_i r₁ r₂ h _ _
    cases r₁; rename_i t₁ _; cases r₂; rename_i t₂ _; cases t₁ <;> cases t₂ <;> simp at h
    . have := HasType.det ‹HasType b Ty.bool› ‹HasType b Ty.nat›; contradiction
    . have := HasType.det ‹HasType a Ty.bool› ‹HasType a Ty.nat›; contradiction
    . have := HasType.det ‹HasType b Ty.bool› ‹HasType b Ty.nat›; contradiction

instance (e : Expr) (t : Ty) : Decidable (HasType e t) :=
  match h' : e.typeCheck with
  | some ⟨t', ht'⟩ =>
    if heq : t = t' then
      isTrue (heq ▸ ht')
    else
      isFalse fun ht => heq (HasType.det ht ht')
  | none => isFalse (Expr.typeCheck_complete h')
