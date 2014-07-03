import standard
using tactic (renaming id->id_tac)

definition id {A : Type} (a : A) := a

definition simple {A : Bool} : tactic
:= unfold @id.{1}; assumption

theorem tst {A B : Bool} (H1 : A) (H2 : B) : id A
:= by simple

check tst
