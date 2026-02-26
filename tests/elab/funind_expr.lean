import Lean.Elab.Tactic.Guard

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

/--
info: Expr.typeCheck.induct (motive : Expr → Prop) (case1 : ∀ (a : Nat), motive (Expr.nat a))
  (case2 : ∀ (a : Bool), motive (Expr.bool a))
  (case3 :
    ∀ (a b : Expr) (h₁ : HasType a Ty.nat) (h₂ : HasType b Ty.nat),
      b.typeCheck = Maybe.found Ty.nat h₂ →
        a.typeCheck = Maybe.found Ty.nat h₁ → motive a → motive b → motive (a.plus b))
  (case4 :
    ∀ (a b : Expr),
      (∀ (h₁ : HasType a Ty.nat) (h₂ : HasType b Ty.nat),
          a.typeCheck = Maybe.found Ty.nat h₁ → b.typeCheck = Maybe.found Ty.nat h₂ → False) →
        motive a → motive b → motive (a.plus b))
  (case5 :
    ∀ (a b : Expr) (h₁ : HasType a Ty.bool) (h₂ : HasType b Ty.bool),
      b.typeCheck = Maybe.found Ty.bool h₂ →
        a.typeCheck = Maybe.found Ty.bool h₁ → motive a → motive b → motive (a.and b))
  (case6 :
    ∀ (a b : Expr),
      (∀ (h₁ : HasType a Ty.bool) (h₂ : HasType b Ty.bool),
          a.typeCheck = Maybe.found Ty.bool h₁ → b.typeCheck = Maybe.found Ty.bool h₂ → False) →
        motive a → motive b → motive (a.and b))
  (e : Expr) : motive e
-/
#guard_msgs in
#check Expr.typeCheck.induct

/-
This no longer works after splitting non-refining tail-call matches,
as we now have different number of variables

theorem Expr.typeCheck_complete {e : Expr} : e.typeCheck = .unknown → ¬ HasType e ty := by
  apply Expr.typeCheck.induct (motive := fun e => e.typeCheck = .unknown → ¬ HasType e ty)
    <;> simp [typeCheck]
    <;> {
      intro _ _ a b iha ihb
      split <;> simp [*]
      intro ht; cases ht
      next hnp h₁ h₂ => exact hnp h₁ h₂ (typeCheck_correct h₁ (iha · h₁)) (typeCheck_correct h₂ (ihb · h₂))
    }
-/

-- The same, using the induction tactic
theorem Expr.typeCheck_complete' {e : Expr} : e.typeCheck = .unknown → ¬ HasType e ty := by
  induction e using typeCheck.induct
  all_goals simp [typeCheck]
  case case3 | case5 => simp [*]
  case case4 iha ihb | case6 iha ihb =>
    intro ht; cases ht
    next hnp h₁ h₂ => exact hnp h₁ h₂ (typeCheck_correct h₁ (iha · h₁)) (typeCheck_correct h₂ (ihb · h₂))
