-- Check that we can write numerals in `Fin (2^n)`
-- even though `2^n` is not a definitionally a successor,
-- via the `NeZero (2^n)` instance.

example {n : Nat} : Fin (2^n) := 0
