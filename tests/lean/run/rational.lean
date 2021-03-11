structure Rat where
  num : Int
  den : Nat
  pos : den > 0

instance (n : Nat) : OfNat Rat n where
  ofNat := {
    num := n
    den := 1
    pos := by decide
  }

instance : Add Rat where
  add a b := {
    num := a.num * b.den + b.num * a.den
    den := a.den * b.den
    pos := sorry
  }

instance : Coe Int Rat where
  coe n := {
    num := n
    den := 1
    pos := by decide
  }

def f1 (x : Rat) (n : Nat) : Rat :=
  x + n + 1

def f2 (x : Rat) (n : Nat) : Rat :=
  1 + x + n

def f3 (x : Rat) (n : Nat) : Rat :=
  1 + n + x + 2

def f4 (x : Rat) (n : Nat) : Rat :=
  n + 1 + x + n
