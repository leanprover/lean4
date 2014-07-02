import standard
using tactic

theorem tst {A B : Bool} (H1 : A) (H2 : B) : A
:= by state; now  |
      state; fail |
      exact

check tst