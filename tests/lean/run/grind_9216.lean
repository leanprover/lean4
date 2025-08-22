module
import Std.Data.HashSet

open Std

example (seen : HashSet Int) (xs : List Int) (x : Int) (h : ¬-x ∈ seen) :
    (∃ a, a ∈ seen.insert x ∧ ∃ b, b ∈ xs ∧ a + b = 0) ↔
    (∃ y, y ∈ xs ∧ x + y = 0) ∨ ∃ a, a ∈ seen ∧ ∃ b, b ∈ x :: xs ∧ a + b = 0 := by
  -- In 4.22.0-rc2, this example used to work without the `simp only` because patterns containing `+` were being selected.
  -- By unfolding `HashSet.mem_insert` before invoking `grind` we change the pattern that is selected. That is, `_ ∈ seen` is selected.
  simp only [HashSet.mem_insert]
  grind

-- The example also works when we restore `HAdd.hAdd` priority.
-- We say this example worked by "accident" before.
attribute [local grind symbol default] HAdd.hAdd in
example (seen : HashSet Int) (xs : List Int) (x : Int) (h : ¬-x ∈ seen) :
    (∃ a, a ∈ seen.insert x ∧ ∃ b, b ∈ xs ∧ a + b = 0) ↔
    (∃ y, y ∈ xs ∧ x + y = 0) ∨ ∃ a, a ∈ seen ∧ ∃ b, b ∈ x :: xs ∧ a + b = 0 := by
  grind

/-
Here is an encoding trick used in the SMT community.
Terms like `x + y` are rarely used in patterns because
they generate too many instances, and because arithmetical
terms are often normalized by SMT solvers. However, for E-matching,
`+` is just another symbol. The E-matcher does not know that it is,
for example, associative and commutative (AC).
If you want to E-match against an arithmetical relation, you can
introduce an auxiliary definition to make the pattern matching more effective.
Example:
-/
@[grind] def IsAddInv (a b : Int) : Prop := a = -b
example (seen : HashSet Int) (xs : List Int) (x : Int) (h : ¬-x ∈ seen) :
    (∃ a, a ∈ seen.insert x ∧ ∃ b, b ∈ xs ∧ IsAddInv a b) ↔
    (∃ y, y ∈ xs ∧ IsAddInv x y) ∨ ∃ a, a ∈ seen ∧ ∃ b, b ∈ x :: xs ∧ IsAddInv a b := by
  grind
