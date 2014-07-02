import standard

definition id {A : Type} (a : A) := a

definition simple_tac {A : Bool} : tactic A
:= unfold_tac @id.{1}; exact_tac

theorem tst {A B : Bool} (H1 : A) (H2 : B) : id A
:= by simple_tac

check tst
