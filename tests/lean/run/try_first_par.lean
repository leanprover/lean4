/-!
# Test for `first_par` combinator in try?

This tests that `try?` uses `first_par` internally to try multiple grind variants
(`grind? +suggestions`, `grind? +locals`, `grind? +locals +suggestions`) in parallel
and return the first successful result.

Note: For simple goals like this, the `atomic` block (which includes `rfl` and basic grind
variants) usually succeeds first, so `first_par` is not reached. The `first_par` is a
fallback for when the atomic tactics fail.
-/

-- A local definition that grind needs to unfold
def myDouble (n : Nat) : Nat := n + n

-- try? finds multiple solutions: rfl works, and grind with the definition also works.
-- The atomic block (which includes grind? [= myDouble]) succeeds first.
/--
info: Try these:
  [apply] rfl
  [apply] grind [= myDouble]
  [apply] grind only [myDouble]
  [apply] grind => instantiate only [myDouble]
-/
#guard_msgs in
example (n : Nat) : myDouble n = n + n := by try?
