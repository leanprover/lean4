structure A where
  a : Nat

structure B where
  a : Nat := 1
  b : Nat

structure C extends A, B

def f (b : Nat) : C :=
  { b }

theorem ex (b : Nat) : (f b).a = 1 :=
  rfl
