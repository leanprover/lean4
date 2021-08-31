structure Foo where
  a : Nat

instance fooAdd : Add Foo where
  add x y := ⟨x.a + y.a⟩

def f1 (a b : Foo) := a + b

section
attribute [-instance] fooAdd

def f2 (a b : Foo) := a + b -- Error
end

def f3 (a b : Foo) := a + b
