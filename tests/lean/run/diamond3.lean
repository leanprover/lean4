structure A where
  a : Nat

structure B where
  a : Nat
  b : Nat
  c : Nat := a + b

structure C extends B where
  d : Nat := 0
  e : Nat := 0

structure D extends A, C

def f (a b : Nat) : D :=
  { a, b }

theorem ex (a b : Nat) : (f a b |>.c) = a + b :=
  rfl
