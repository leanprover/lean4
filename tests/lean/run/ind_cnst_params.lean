inductive foo
| mk (a : nat) (b : nat) : bool → foo

print foo.mk

check foo.mk 0 0 tt

universe variables u

inductive List (α : Type u)
| nil {} (a : nat) : List
| cons (hd : α) (tail : List) : List

check List.cons "a" (List.nil 1)
check List.cons "a" (List.nil 2)
