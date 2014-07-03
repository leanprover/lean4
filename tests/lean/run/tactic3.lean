import standard
using tactic

theorem tst {A B : Bool} (H1 : A) (H2 : B) : A
:= by trace "first";  state; now  |
      trace "second"; state; fail |
      trace "third";  assumption

check tst