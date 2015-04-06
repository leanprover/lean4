import logic
open tactic

theorem tst {A B : Prop} (H1 : A) (H2 : B) : A
:= by (trace "first";  state; now  |
       trace "second"; state; fail |
       trace "third";  assumption)

check tst
