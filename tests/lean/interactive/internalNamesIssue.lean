namespace Foo

def foo (x : Nat) := x + x + x

def bla (x : Nat) : Nat :=
  if x > foo (10 + 10) then 1 else x * x * x

end Foo

#check Foo.
         --^ textDocument/completion
