open tactic

namespace test

inductive enum1 : Type := ea | eb | ec | ed

attribute [instance]
definition enum1_dec_eq : decidable_eq enum1 :=
by mk_dec_eq_instance

inductive Expr :=
| var  : nat → Expr
| app  : ∀ (n : nat) (e1 : Expr) (e2 : Expr) (e3 : Expr) (e4 : Expr),  Expr
| Elet : Expr → Expr
| bla  : list nat → Expr

attribute [instance]
definition Expr_has_dec_eq : decidable_eq Expr :=
by mk_dec_eq_instance

definition prod_decidable {A : Type} {B : Type} [decidable_eq A] [decidable_eq B] : decidable_eq (A × B) :=
by mk_dec_eq_instance

definition sum_decidable {A : Type} {B : Type} [decidable_eq A] [decidable_eq B] : decidable_eq (sum A B) :=
by mk_dec_eq_instance

definition nat_decidable : decidable_eq nat :=
by mk_dec_eq_instance

definition list_decidable {A : Type} [decidable_eq A] : decidable_eq (list A) :=
by mk_dec_eq_instance

definition option_decidable {A : Type} [decidable_eq A] : decidable_eq (option A) :=
by mk_dec_eq_instance

end test
