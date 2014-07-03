import standard
using tactic

theorem tst {A B : Bool} (H1 : A) (H2 : B) : ((fun x : Bool, x) A) ∧ B ∧ A
:= by apply and_intro; beta; assumption; apply and_intro; !assumption

