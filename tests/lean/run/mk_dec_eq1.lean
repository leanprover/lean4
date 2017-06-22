open tactic

namespace test

inductive enum1 : Type | ea | eb | ec | ed

instance enum1_dec_eq : decidable_eq enum1 :=
by mk_dec_eq_instance

inductive Expr
| var  : nat → Expr
| app  : ∀ (n : nat) (e1 : Expr) (e2 : Expr) (e3 : Expr) (e4 : Expr),  Expr
| Elet : Expr → Expr
| bla  : list nat → Expr

instance Expr_has_dec_eq : decidable_eq Expr :=
by mk_dec_eq_instance
universe variables u v
def prod_decidable {A : Type u} {B : Type v} [decidable_eq A] [decidable_eq B] : decidable_eq (A × B) :=
by mk_dec_eq_instance

def sum_decidable {A : Type u} {B : Type v} [decidable_eq A] [decidable_eq B] : decidable_eq (sum A B) :=
by mk_dec_eq_instance

def nat_decidable : decidable_eq nat :=
by mk_dec_eq_instance

def list_decidable {A : Type u} [decidable_eq A] : decidable_eq (list A) :=
by mk_dec_eq_instance

def option_decidable {A : Type v} [decidable_eq A] : decidable_eq (option A) :=
by mk_dec_eq_instance

end test
