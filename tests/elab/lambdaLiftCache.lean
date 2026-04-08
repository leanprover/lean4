def map (f : Nat → Nat) (xs : List Nat) :=
  xs.map f

set_option trace.Compiler.saveMono true

def foo (x : Nat) (xs : List Nat) :=
  map (· + x) xs

def boo (x : Nat) (xs : List Nat) :=
  map (· + x) xs
