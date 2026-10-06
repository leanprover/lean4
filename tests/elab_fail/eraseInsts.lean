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

-- Same, with an explicit result type so that the failed query is metavariable-free and its
-- cached failure reaches the persistent (cross-command) cache tier.
section
attribute [-instance] fooAdd

def g2 (a b : Foo) : Foo := a + b -- Error
end

def g3 (a b : Foo) : Foo := a + b
