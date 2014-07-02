import logic
import tactic

theorem tst {A B : Bool} (H1 : A) (H2 : B) : A
:= by state_tac; exact_tac

check tst