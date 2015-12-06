import data.list
set_option blast.strategy "cc"

definition t1 (a b : nat) : (a = b) ↔ (b = a) :=
by blast

print t1

definition t2 (a b : nat) : (a = b) = (b = a) :=
by blast

print t2

definition t3 (a b : nat) : (a = b) == (b = a) :=
by blast

print t3

open perm

definition t4 (a b : list nat) : (a ~ b) ↔ (b ~ a) :=
by blast

definition t5 (a b : list nat) : (a ~ b) = (b ~ a) :=
by blast

definition t6 (a b : list nat) : (a ~ b) == (b ~ a) :=
by blast

definition t7 (p : Prop) (a b : nat) : a = b → b ≠ a → p :=
by blast

definition t8 (a b : Prop) : (a ↔ b) → ((b ↔ a) ↔ (a ↔ b)) :=
by blast

definition t9 (a b c : nat) : b = c → (a = b ↔ c = a) :=
by blast

definition t10 (a b c : list nat) : b ~ c → (a ~ b ↔ c ~ a) :=
by blast

definition t11 (a b c : list nat) : b ~ c → ((a ~ b) = (c ~ a)) :=
by blast
