open Lean

structure S where
  carrier : Type
  mul : carrier → carrier → carrier

def Nat.S : S where
  carrier := Nat
  mul := (· * ·)

def Int.S : S where
  carrier := Int
  mul := (· * ·)

@[unificationHint]
def NatHint (s : S) : UnificationHint where
 pattern := s.carrier =?= Nat
 constraints := [ s =?= Nat.S ]

@[unificationHint]
def IntHint (s : S) : UnificationHint where
 pattern := s.carrier =?= Int
 constraints := [ s =?= Int.S ]

def mul {s : S} (a b : s.carrier) : s.carrier :=
  s.mul a b

def square (x : Nat) : Nat :=
  mul x x

set_option pp.all true
#print square

#check fun x : Nat => mul x x

#check fun y : Int => mul y y

def BV (n : Nat) := { a : Array Bool // a.size = n }

def sext (x : BV s) (n : Nat) : BV (s+n) :=
  ⟨mkArray (s+n) false, Array.sizeMkArrayEq ..⟩

def bvmul (x y : BV w) : BV w :=
  x

@[unificationHint]
def add64Eq128Hint (x : Nat) : UnificationHint where
 pattern := Nat.add 64 x =?= 128
 constraints := [ x =?= 64 ]

set_option pp.all false

def tst (x y : BV 64) : BV 128 :=
  bvmul (sext x 64) (sext y _)
