variable {α} [ToString α] (n : Nat)

local macro "foo" : term => `(n)

def f :=
  foo

#check f 10
