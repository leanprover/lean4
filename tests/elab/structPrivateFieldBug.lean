structure A where
  private x : Nat := 10

def g (a : Nat) : A :=
  {}

theorem ex1 (a : Nat) : (g a |>.x) = 10 :=
  rfl

structure B extends A where
  y : Nat

def f (a : Nat) : B :=
  { y := a }

theorem ex2 (a : Nat) : (f a |>.x) = 10 :=
  rfl
