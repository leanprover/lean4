import logic
open tactic (renaming id->id_tac)

definition id {A : Type} (a : A) := a

theorem tst {A B : Prop} (H1 : A) (H2 : B) : id A
:= by unfold id; assumption

check tst
