def ex1 (x y : Nat) (i j : Int) :=
  binrel! Less x i

def ex2 (x y : Nat) (i j : Int) :=
  binrel! Less i x

def ex3 (x y : Nat) (i j : Int) :=
  binrel! Less (i + 1) x

def ex4 (x y : Nat) (i j : Int) :=
  binrel! Less i (x + 1)

def ex5 (x y : Nat) (i j : Int) :=
  binrel! Less i (x + y)

def ex6 (x y : Nat) (i j : Int) :=
  binrel! Less (i + j) (x + 0)

def ex7 (x y : Nat) (i j : Int) :=
  binrel! Less (i + j) (x + i)

def ex8 (x y : Nat) (i j : Int) :=
  binrel! Less (i + 0) (x + i)

def ex9 (n : UInt32) :=
  binrel! Less n 0xd800

def ex10 (x : Lean.Syntax) : Bool :=
  x.getArgs.all (binrel! BEq.beq ·.getKind `foo)

def ex11 (xs : Array (Nat × Nat)) :=
  let f a b := binrel! Less a.1 b.1
  f xs[1] xs[2]
