import standard

definition id {A : Type} (a : A) := a

theorem tst {A B : Bool} (H1 : A) (H2 : B) : id A
:= by !(unfold_tac @id; state_tac); exact_tac

check tst