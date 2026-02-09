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

theorem ex1 (a b : Nat) : (f a b |>.c) = a + b :=
  rfl

structure C' extends B where
  d : Nat
  e : Nat
  c := d + e

structure D' extends A, C'

def f' (a b d e: Nat) : D' :=
  { a, b, d, e }

theorem ex2 (a b d e: Nat) : (f' a b d e |>.c) = d + e :=
  rfl

structure D'' extends A, C' where
  c := a

def f'' (a b d e : Nat) : D'' :=
  { a, b, d, e }

theorem ex3 (a b d e: Nat) : (f'' a b d e |>.c) = a :=
  rfl

structure B1 where
  a : Nat
  b : Nat

structure C1 extends B1 where
  d : Nat
  e : Nat
  c : Nat := b + e

structure D1 extends A, C1

def f1 (a b d e : Nat) : D1 :=
  { a, b, d, e }

theorem ex4 (a b d e: Nat) : (f1 a b d e |>.c) = b + e :=
  rfl

structure B2 where
  a : Nat
  b : Nat
  c : Nat

structure C2 extends B2 where
  d : Nat
  e : Nat
  c := b + e

structure D2 extends A, C2

def f2 (a b d e : Nat) : D2 :=
  { a, b, d, e }

theorem ex5 (a b d e: Nat) : (f2 a b d e |>.c) = b + e :=
  rfl
