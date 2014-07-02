import standard
using tactic

theorem tst {A B : Bool} (H1 : A) (H2 : B) : A ∧ B ∧ A
:= by apply and_intro; state; exact; apply and_intro; !exact
check tst

theorem tst2 {A B : Bool} (H1 : A) (H2 : B) : A ∧ B ∧ A
:= by !((apply @and_intro | exact) ; trace "STEP"; state; trace "----------")

check tst2

