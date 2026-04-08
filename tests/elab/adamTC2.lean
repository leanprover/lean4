inductive Expr where
  | nat  : Nat → Expr
  | plus : Expr → Expr → Expr
  | bool : Bool → Expr
  | and  : Expr → Expr → Expr

inductive Ty where
  | nat
  | bool
  deriving DecidableEq

inductive HasType : Expr → Ty → Prop
  | nat  : HasType (.nat v) .nat
  | plus : HasType a .nat → HasType b .nat → HasType (.plus a b) .nat
  | bool : HasType (.bool v) .bool
  | and  : HasType a .bool → HasType b .bool → HasType (.and a b) .bool

inductive Maybe (p : α → Prop) where
  | unknown
  | found : (a : α) → p a → Maybe p

notation "{{ " x " | " p " }}" => Maybe (fun x => p)

def Expr.typeCheck (e : Expr) : {{ ty | HasType e ty }} :=
  match e with
  | nat ..   => .found .nat .nat
  | bool ..  => .found .bool .bool
  | plus a b =>
    match a.typeCheck, b.typeCheck with
    | .found .nat h₁, .found .nat h₂ => .found .nat (.plus h₁ h₂)
    | _, _ => .unknown
  | and a b =>
    match a.typeCheck, b.typeCheck with
    | .found .bool h₁, .found .bool h₂ => .found .bool (.and h₁ h₂)
    | _, _ => .unknown

theorem HasType.det (h₁ : HasType e t₁) (h₂ : HasType e t₂) : t₁ = t₂ := by
  cases h₁ <;> cases h₂ <;> rfl

-- TODO: for simplifying the following proof we need: ematching for forward reasoning, and `match` blast for case analysis

theorem Expr.typeCheck_complete {e : Expr} : e.typeCheck = .unknown → ¬ HasType e t := by
  induction e with simp [typeCheck]
  | plus a b iha ihb =>
    revert iha ihb
    cases typeCheck a <;> cases typeCheck b <;> simp <;> intros <;> intro h <;> cases h <;> try contradiction
    rename_i ty₁ _ ty₂ _ h _ _
    cases ty₁ <;> cases ty₂ <;> simp at h
    . have := HasType.det ‹HasType b Ty.bool› ‹HasType b Ty.nat›; contradiction
    . have := HasType.det ‹HasType a Ty.bool› ‹HasType a Ty.nat›; contradiction
    . have := HasType.det ‹HasType a Ty.bool› ‹HasType a Ty.nat›; contradiction
  | and a b iha ihb =>
    revert iha ihb
    cases typeCheck a <;> cases typeCheck b <;> simp <;> intros <;> intro h <;> cases h <;> try contradiction
    rename_i ty₁ _ ty₂ _ h _ _
    cases ty₁ <;> cases ty₂ <;> simp at h
    . have := HasType.det ‹HasType b Ty.bool› ‹HasType b Ty.nat›; contradiction
    . have := HasType.det ‹HasType a Ty.bool› ‹HasType a Ty.nat›; contradiction
    . have := HasType.det ‹HasType b Ty.bool› ‹HasType b Ty.nat›; contradiction

instance (e : Expr) (t : Ty) : Decidable (HasType e t) :=
  match h' : e.typeCheck with
  | .found t' ht' =>
    if heq : t = t' then
      isTrue (heq ▸ ht')
    else
      isFalse fun ht => heq (HasType.det ht ht')
  | .unknown => isFalse (Expr.typeCheck_complete h')
