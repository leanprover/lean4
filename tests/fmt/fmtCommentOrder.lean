/-!
Tests that several comments after the same token keep their order.
-/

def a := 1
def f (x : Nat) : Nat := x

def typeAscription := (a /- first -/ /- second -/ /- third -/ : Nat)

def beforeOperator := a /- first -/ /- second -/ + 2

def application := f /- first -/ /- second -/ a

def binder (x : Nat) /- first -/ /- second -/ : Nat := x

structure S where
  x : Nat /- first -/ /- second -/
  y : Nat

def blockThenLine := a /- first -/ -- second

def endOfCommand := a /- first -/ /- second -/
