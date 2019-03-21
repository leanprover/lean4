structure S :=
(a : Nat) (h : a > 0) (b : Nat)

def f (s : S) :=
s.b - s.a

#exit

#eval f {a := 5, b := 30, h := sorry }
