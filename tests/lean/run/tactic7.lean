import logic
open tactic

theorem tst {A B : Prop} (H1 : A) (H2 : B) : A ∧ B ∧ A
:= by apply and.intro; state; assumption; apply and.intro; !assumption
check tst

theorem tst2 {A B : Prop} (H1 : A) (H2 : B) : A ∧ B ∧ A
:= by repeat ((apply @and.intro | assumption) ; trace "STEP"; state; trace "----------")

check tst2
