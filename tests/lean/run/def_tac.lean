context
  open tactic
  definition cases_refl (e : expr) : tactic :=
  cases e expr_list.nil; apply rfl

  definition cases_lst_refl : expr_list → tactic
  | cases_lst_refl expr_list.nil        := apply rfl
  | cases_lst_refl (expr_list.cons a l) := cases a expr_list.nil; cases_lst_refl l

  -- Similar to cases_refl, but make sure the argument is not an arbitrary expression.
  definition eq_rec {A : Type} {a b : A} (e : a = b) : tactic :=
  cases e expr_list.nil; apply rfl
end

notation `cases_lst` l:(foldr `,` (h t, tactic.expr_list.cons h t) tactic.expr_list.nil) := cases_lst_refl l

open prod
theorem tst₁ (a : nat × nat) : (pr1 a, pr2 a) = a :=
by cases_refl a

theorem tst₂ (a b : nat × nat) (h₁ : pr₁ a = pr₁ b) (h₂ : pr₂ a = pr₂ b) : a = b :=
by cases_lst a, b, h₁, h₂

open nat
theorem tst₃ (a b : nat) (h : a = b) : a + b = b + a :=
by eq_rec h
