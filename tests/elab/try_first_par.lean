import Lean.LibrarySuggestions.Default

/-!
# Test for `first_par` combinator in try?

This tests that `try?` uses `first_par` internally to try multiple grind variants
(`grind? +suggestions`, `grind? +locals`, `grind? +locals +suggestions`) in parallel
and return the first successful result.

The test creates a scenario where:
1. Basic tactics (rfl, assumption, simp) fail
2. Basic grind fails
3. But `grind +locals +suggestions` succeeds by finding a local theorem via library search
-/

structure MyPair (α : Type) where
  fst : α
  snd : α

def foo (x : MyPair Nat) := x

-- A theorem about MyPair that grind +suggestions can find via library search
theorem myPair_eq (p : MyPair Nat) (h1 : p.fst = 1) (h2 : p.snd = 1) :
    p = foo ⟨1, 1⟩ := by
  cases p; simp_all [foo]

-- A goal where:
-- - atomic block fails (no simple solution, basic grind can't prove it)
-- - first_par succeeds: grind +locals +suggestions finds myPair_eq
-- The +locals +suggestions flags are filtered out in the suggestion output
/--
info: Try these:
  [apply] grind only [myPair_eq, foo]
  [apply] grind =>
    instantiate only [myPair_eq]
    instantiate only [foo]
-/
#guard_msgs in
example (p : MyPair Nat) (h1 : p.fst = 1) (h2 : p.snd = 1) : p = ⟨1, 1⟩ := by
  fail_if_success grind
  fail_if_success grind +locals
  fail_if_success grind +suggestions
  try?
