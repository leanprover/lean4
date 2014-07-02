import logic
import tactic
using tactic

theorem tst {A B : Bool} (H1 : A) (H2 : B) : A
:= by state_tac; now_tac  |
      state_tac; fail_tac |
      exact_tac

check tst