structure S :=
(a : nat) (h : a > 0) (b : nat)

def f (s : S) :=
s.b - s.a

#eval f {a := 5, b := 30, h := sorry }
