--
definition foo1 (a b c) := a + b + (c:nat)

definition foo2 (a : nat) (b c) := a + b + c

definition foo3 (a b) (c : nat) := a + b + c

definition foo4 (a b c : nat) := a + b + c

definition foo5 (a b c) : nat := a + b + c

definition foo6 {a b c} : nat := a + b + c

-- definition foo7 a b c : nat := a + b + c  -- Error

definition foo8 (a b c : nat) : nat := a + b + c

definition foo9 (a : nat) (b : nat) (c : nat) : nat := a + b + c

definition foo10 (a : nat) (b) (c : nat) : nat := a + b + c
