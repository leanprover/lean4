def foo {α} (a : Option α) (b : α) : α  :=
match a with
| some a => a
| none   => b

structure S :=
(x : Nat)

#check if 0 == 1 then true else false

def f (x : Nat) : Nat :=
if x < 5 then x+1 else x-1

def x := 1

#check foo x x

#check match 1 with | x => x + 1
#check match 1 : Int -> _ with | x => x + 1
#check match 1 with | x => x + 1
#check match 1 : Int -> _ with | x => x + 1

def g (x : Nat × Nat) (y : Nat) :=
x.1 + x.2 + y

#check (g ⟨·, 1⟩ ·)
