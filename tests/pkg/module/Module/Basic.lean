module

/-! Module docstring -/

/-- A definition. -/
def f := 1

/-- A theorem. -/
theorem t : f = 1 := sorry

theorem trfl : f = 1 := rfl

@[expose] def fexp := 1

private def priv := 2

/-! Private decls should not be accessible in exported contexts. -/

/-- error: unknown identifier 'priv' -/
#guard_msgs in
abbrev h := priv
