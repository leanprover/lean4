def f1 (a : Array Nat) (i : Nat) :=
  a[i]

def f2 (a : Array Nat) (i : Fin a.size) :=
  a[i] -- Ok

def f3 (a : Array Nat) (h : n ≤ a.size) (i : Fin n) :=
  a[i] -- Ok

opaque a : Array Nat
opaque n : Nat
axiom n_lt_a_size : n < a.size

def f4 (i : Nat) (h : i < n) :=
  have : i < a.size := Nat.lt_trans h n_lt_a_size
  a[i]

def f5 (i : Nat) (h : i < n) :=
  a[i]'(Nat.lt_trans h n_lt_a_size)

def f6 (i : Nat) :=
  a[i]!
