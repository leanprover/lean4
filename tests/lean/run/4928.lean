/--
error: tactic 'fail' failed
x y : Nat
⊢ x - 1 < x
-/
#guard_msgs in
def g (x : Nat) (y : Nat) : Nat := g (x - 1) y
termination_by x
decreasing_by fail

/--
error: tactic 'fail' failed
x : List Nat
y : Nat
⊢ sizeOf x.tail < sizeOf x
-/
#guard_msgs in
def h (x : List Nat) (y : Nat) : Nat := h x.tail y
termination_by x
decreasing_by fail

/--
error: tactic 'fail' failed
x : List Nat
y : Nat
⊢ x.tail.length < x.length
-/
#guard_msgs in
def f (x : List Nat) (y : Nat) : Nat := f x.tail y
termination_by x.length
decreasing_by fail

/--
error: tactic 'fail' failed
x : List Nat
y : Nat
⊢ x.tail.length < x.length
-/
#guard_msgs in
mutual
def f1 (x : List Nat) (y : Nat) : Nat := f2 x.tail y
termination_by x.length
decreasing_by fail
def f2 (x : List Nat) (y : Nat) : Nat := f1 x.tail y
termination_by x.length
decreasing_by fail
end
