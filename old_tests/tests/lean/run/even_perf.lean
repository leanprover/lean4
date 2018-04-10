open nat

def even : nat → bool
| 0               := tt
| (succ 0)        := ff
| (succ (succ n)) := even n

#eval even 0
#eval even 1
#eval even 2
#eval even 10000
#eval even 10001
