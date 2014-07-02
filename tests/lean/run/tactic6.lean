import standard
using tactic (renaming id->id_tac)

definition id {A : Type} (a : A) := a

theorem tst {A B : Bool} (H1 : A) (H2 : B) : id A
:= by unfold id; exact

check tst
