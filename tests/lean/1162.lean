inductive weekday : Type
| sunday : weekday
| monday : weekday
| tuesday : weekday
| wednesday : weekday

def ppday (d : weekday) : nat :=
match d with
| sunday    := 0
| monday    := 1
| tuesday   := 2
| wednesday := 3
end
