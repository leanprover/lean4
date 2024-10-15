structure SomeStructure where
  n : Nat

def SomeStructure.foo1 (s : SomeStructure) : Nat := s.n

/-- A docstring. -/
def SomeStructure.foo2 (s : SomeStructure) : Nat := s.n

@[deprecated] def SomeStructure.foo3 (s : SomeStructure) : Nat := s.n

/-- A docstring. -/
@[deprecated] def SomeStructure.foo4 (s : SomeStructure) : Nat := s.n

@[deprecated SomeStructure.foo1] def SomeStructure.foo5 (s : SomeStructure) : Nat := s.n

/-- A docstring. -/
@[deprecated SomeStructure.foo1] def SomeStructure.foo6 (s : SomeStructure) : Nat := s.n

@[deprecated "`SomeStructure.foo7` has been deprecated; please use `SomeStructure.foo1` instead."]
def SomeStructure.foo7 (s : SomeStructure) : Nat := s.n

/-- A docstring. -/
@[deprecated "`SomeStructure.foo8` has been deprecated; please use `SomeStructure.foo1` instead."]
def SomeStructure.foo8 (s : SomeStructure) : Nat := s.n

example := SomeStructure.foo  -- Completion items with a deprecation tag and a deprecation message
                          --^ textDocument/completion
