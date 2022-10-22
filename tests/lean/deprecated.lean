set_option linter.deprecated true

def g (x : Nat) := x + 1

@[deprecated g]
def f (x : Nat) := x + 1

@[deprecated]
def h (x : Nat) := x + 1

#eval f 0 + 1

#eval h 0

@[deprecated g1]
def f1 (x : Nat) := x + 1

def Foo.g1 := 10

@[deprecated Foo.g1]
def f2 (x : Nat) := x + 1

@[deprecated g1]
def f3 (x : Nat) := x + 1

open Foo
@[deprecated g1]
def f4 (x : Nat) := x + 1

#eval f2 0 + 1
set_option linter.deprecated false in
#eval f2 0 + 1
#eval f4 0 + 1
