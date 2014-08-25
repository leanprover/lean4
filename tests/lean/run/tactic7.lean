import logic
using tactic

theorem tst {A B : Prop} (H1 : A) (H2 : B) : A ∧ B ∧ A
:= by apply and_intro; state; assumption; apply and_intro; !assumption
check tst

theorem tst2 {A B : Prop} (H1 : A) (H2 : B) : A ∧ B ∧ A
:= by !([apply @and_intro | assumption] ; trace "STEP"; state; trace "----------")

check tst2
