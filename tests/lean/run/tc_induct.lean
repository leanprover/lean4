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

theorem HasType.det (h₁ : HasType e t₁) (h₂ : HasType e t₂) : t₁ = t₂ := by
  cases h₁ <;> cases h₂ <;> rfl

inductive Maybe (p : α → Prop) where
  | found : (a : α) → p a → Maybe p
  | unknown

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
termination_by e

theorem Expr.typeCheck_correct (h₁ : HasType e ty) (h₂ : e.typeCheck ≠ .unknown)
        : e.typeCheck = .found ty h := by
  revert h₂
  cases typeCheck e with
  | found ty' h' => intro; have := HasType.det h₁ h'; subst this; rfl
  | unknown => intros; contradiction

derive_functional_induction Expr.typeCheck
#check Expr.typeCheck.induct

theorem Expr.typeCheck_complete {e : Expr} : e.typeCheck = .unknown → ¬ HasType e ty := by
  apply Expr.typeCheck.induct (motive := fun e => e.typeCheck = .unknown → ¬ HasType e ty)
    <;> simp [typeCheck]
    <;> {
      intro a b iha ihb
      split <;> simp [*]
      intro ht; cases ht
      next hnp h₁ h₂ => exact hnp h₁ h₂ (typeCheck_correct h₁ (iha · h₁)) (typeCheck_correct h₂ (ihb · h₂))
    }
