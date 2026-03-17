def f1 (x : Nat) : Nat :=
  let rec g (x : Nat) := x + 1 -- f1.g already declared
  let rec g (x : Nat) := x + 2
  g x

def f2 (x : Nat) : Nat :=
  let g1 (x : Nat) :=
    let rec h (x : Nat) := x + 1
    h x
  let g2 (x : Nat) :=
    let rec h (x : Nat) := x + 2 -- error f.h already declared
    h x
  g1 x + g2 x

def f3.h := 10

def f3 (x : Nat) : Nat :=
  let rec h (x : Nat) := x + 2 -- error f3.h already declared
  h x

def f4 (x : Nat) : Nat :=
  let rec g1 (x : Nat) :=
    let rec h (x : Nat) := x + 1  -- this is f4.g1.h
    h x
  let rec g2 (x : Nat) :=
    let rec h (x : Nat) := x + 2  -- this is f4.g2.h
    h x
  g1 x + g2 x

theorem ex1 (x : Nat) : f4 x = (x + 1) + (x + 2) :=
  rfl

theorem ex2 (x : Nat) : f4.g1.h x = x + 1 :=
  rfl

theorem ex3 (x : Nat) : f4.g2.h x = x + 2 :=
  rfl
