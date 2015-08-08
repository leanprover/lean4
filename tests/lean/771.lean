set_option pp.all true
definition id_1 (n : nat) :=
   by exact n

definition id_2 (n : nat) :=
   ((by exact n) : nat)

definition id_3 (n : nat) : nat :=
by exact n

definition id_4 (n : nat) :=
show nat, by exact n
