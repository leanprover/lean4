theorem ex1 : ∀ x : Int, ∃ n : Nat, n > x :=
  sorry

theorem ex2 : ∀ x : Int, ∃ n : Nat, x > n :=
  sorry

namespace Lt

def ex1 (x y : Nat) (i j : Int) :=
  x < i

def ex2 (x y : Nat) (i j : Int) :=
  i < x

def ex3 (x y : Nat) (i j : Int) :=
  i + 1 < x

def ex4 (x y : Nat) (i j : Int) :=
  i < x + 1

def ex5 (x y : Nat) (i j : Int) :=
  i < x + y

def ex6 (x y : Nat) (i j : Int) :=
  i + j < x + 0

def ex7 (x y : Nat) (i j : Int) :=
  i + j < x + i

def ex8 (x y : Nat) (i j : Int) :=
  i + 0 < x + i

def ex9 (n : UInt32) :=
  n < 0xd800

end Lt

namespace Eq

def ex1 (x y : Nat) (i j : Int) :=
  x = i

def ex2 (x y : Nat) (i j : Int) :=
  i = x

def ex3 (x y : Nat) (i j : Int) :=
  i + 1 = x

def ex4 (x y : Nat) (i j : Int) :=
  i = x + 1

def ex5 (x y : Nat) (i j : Int) :=
  i = x + y

def ex6 (x y : Nat) (i j : Int) :=
  i + j = x + 0

def ex7 (x y : Nat) (i j : Int) :=
  i + j = x + i

def ex8 (x y : Nat) (i j : Int) :=
  i + 0 = x + i

def ex9 (n : UInt32) :=
  n = 0xd800

end Eq

namespace BEq

def ex1 (x y : Nat) (i j : Int) :=
  x == i

def ex2 (x y : Nat) (i j : Int) :=
  i == x

def ex3 (x y : Nat) (i j : Int) :=
  i + 1 == x

def ex4 (x y : Nat) (i j : Int) :=
  i == x + 1

def ex5 (x y : Nat) (i j : Int) :=
  i == x + y

def ex6 (x y : Nat) (i j : Int) :=
  i + j == x + 0

def ex7 (x y : Nat) (i j : Int) :=
  i + j == x + i

def ex8 (x y : Nat) (i j : Int) :=
  i + 0 == x + i

def ex9 (n : UInt32) :=
  n == 0xd800

end BEq
