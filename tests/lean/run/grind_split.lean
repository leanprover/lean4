set_option trace.grind.split true
set_option trace.grind.eqc true
example (p q : Prop) : p ∨ q → p ∨ ¬q → ¬p ∨ q → ¬p ∨ ¬q → False := by
  grind

opaque R : Nat → Prop

example (p : Prop) [Decidable p] (a b c : Nat) : (if p then a else b) = c → R a → R b → R c := by
  grind


namespace grind_test_induct_pred

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

theorem HasType.det (h₁ : HasType e t₁) (h₂ : HasType e t₂) : t₁ = t₂ := by
  grind

end grind_test_induct_pred
