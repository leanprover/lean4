open nat

def even : nat → bool
| 0               := tt
| (succ 0)        := ff
| (succ (succ n)) := even n

vm_eval even 0
vm_eval even 1
vm_eval even 2
vm_eval even 10000
vm_eval even 10001
