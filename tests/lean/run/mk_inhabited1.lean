open tactic

definition nat_inhabited : inhabited nat :=
by mk_inhabited_instance

definition list_inhabited {A : Type} : inhabited (list A) :=
by mk_inhabited_instance

definition prod_inhabited {A B : Type} [inhabited A] [inhabited B] : inhabited (A × B) :=
by mk_inhabited_instance

definition sum_inhabited₁ {A B : Type} [inhabited A] : inhabited (sum A B) :=
by mk_inhabited_instance

definition sum_inhabited₂ {A B : Type} [inhabited B] : inhabited (sum A B) :=
by mk_inhabited_instance
