import logic

theorem tst {A B : Bool} (H1 : A) (H2 : B) : A
:= by [echo "executing simple tactic", assumption]
