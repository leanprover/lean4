
theorem test (n : nat) (h : n = n) : true := trivial

example (h : 3 = 3) : true :=
by apply test; assumption

example (h : 3 = 3) : true :=
by apply test; [assumption]
