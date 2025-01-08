set_option trace.grind.split true
set_option trace.grind.eqc true
example (p q : Prop) : p ∨ q → p ∨ ¬q → ¬p ∨ q → ¬p ∨ ¬q → False := by
  grind

opaque R : Nat → Prop

/--
info: [grind] working on goal `grind`
[grind.eqc] (if p then a else b) = c
[grind.eqc] R a = True
[grind.eqc] R b = True
[grind.eqc] R c = False
[grind.split] if p then a else b, generation: 0
[grind] working on goal `grind.1`
[grind.eqc] p = True
[grind.eqc] (if p then a else b) = a
[grind.eqc] R a = R c
[grind] closed `grind.1`
[grind] working on goal `grind.2`
[grind.eqc] p = False
[grind.eqc] (if p then a else b) = b
[grind.eqc] R b = R c
[grind] closed `grind.2`
-/
#guard_msgs (info) in
set_option trace.grind true in
example (p : Prop) [Decidable p] (a b c : Nat) : (if p then a else b) = c → R a → R b → R c := by
  grind

example (p : Prop) [Decidable p] (a b c : Nat) : (if p then a else b) = c → R a → R b → R c := by
  fail_if_success grind (splitIte := false)
  sorry

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

set_option trace.grind true
theorem HasType.det (h₁ : HasType e t₁) (h₂ : HasType e t₂) : t₁ = t₂ := by
  grind

theorem HasType.det' (h₁ : HasType e t₁) (h₂ : HasType e t₂) : t₁ = t₂ := by
  fail_if_success grind (splitIndPred := false)
  sorry

end grind_test_induct_pred
