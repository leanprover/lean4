module

/-! Regression test for issue #14348: opaque constants of a unit-like type are definitionally equal. -/

opaque a : Unit
opaque b : Unit

example : a = b := rfl
