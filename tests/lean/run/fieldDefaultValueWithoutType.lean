
structure S :=
(x := true)

def f (s : S) : Bool :=
s.x

#guard f {}

theorem ex : f {} = true :=
rfl
