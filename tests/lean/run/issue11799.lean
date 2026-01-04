-- Reproducer for issue #11799
-- Panic in async elaboration for theorems with a docstring within `where`

-- Main reproducer: theorem with docstring on where-bound auxiliary
theorem foo : True := aux where /-- doc -/ aux := True.intro

-- Variant: def with docstring (this always worked)
def bar : True := aux where /-- doc -/ aux := True.intro

-- Variant: multiple where-bound auxiliaries with docstrings
theorem baz : True ∧ True := ⟨aux1, aux2⟩ where
  /-- first aux -/ aux1 := True.intro
  /-- second aux -/ aux2 := True.intro

-- Verify the docstrings are actually attached
/-- info: foo.aux : True -/
#guard_msgs in
#check @foo.aux
