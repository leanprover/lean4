new_frontend

structure A :=
(x : Nat := 10)

syntax "{" "}"  : term -- overload `{ }` notation

def f : A :=
{ }

theorem ex : f = { x := 10 } :=
rfl

#check f
