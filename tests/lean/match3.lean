new_frontend

def f (x : Nat) : Nat :=
match x with
| 30  => 31
| y+1 => y
| 0   => 10

#eval f 20
#eval f 0
#eval f 30
