#check expr
#check expr ff
def f (x := 3) (y : nat) := y
#check f 3 4
set_option pp.implicit true
#check expr
