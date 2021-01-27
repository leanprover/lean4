
structure S :=
(x := true)

def f (s : S) : Bool :=
s.x

#eval f {}

theorem ex : f {} = true :=
rfl
