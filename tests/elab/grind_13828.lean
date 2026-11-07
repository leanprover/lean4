module

/-!
Regression test for #13828: `grind?` suggestions used to omit `cases` parameters
(e.g., `cases Bool`), producing suggestions that failed during replay. The parameters
marking types for case-splitting must be preserved in the suggestions.
-/

/--
info: Try these:
  [apply] grind only [#b20c, cases Bool]
  [apply] grind only [cases Bool]
  [apply] grind [cases Bool] => cases #b20c
-/
#guard_msgs (info) in
example (f : Bool → Bool) (x : Bool) (h₁ : f true = true) (h₂ : f false = true) :
    f (f (f x)) = f x := by
  grind? only [cases Bool]

/--
info: Try these:
  [apply] grind only [#b20c, #80cc, cases Option]
  [apply] grind only [cases Option]
  [apply] grind [cases Option] => cases #b20c <;> instantiate only [#80cc]
-/
#guard_msgs (info) in
example (x : Option Nat) : x = none ∨ ∃ n, x = some n := by
  grind? [cases Option]

/-! Check that the suggestions above actually work. -/

example (f : Bool → Bool) (x : Bool) : f (f (f x)) = f x := by
  cases h₁ : f true <;> cases h₂ : f false <;> grind only [#b20c, cases Bool]

example (f : Bool → Bool) (x : Bool) : f (f (f x)) = f x := by
  cases h₁ : f true <;> cases h₂ : f false <;> grind only [cases Bool]

example (f : Bool → Bool) (x : Bool) : f (f (f x)) = f x := by
  cases h₁ : f true <;> cases h₂ : f false <;> grind [cases Bool] => cases #b20c

example (x : Option Nat) : x = none ∨ ∃ n, x = some n := by
  grind only [#b20c, #80cc, cases Option]

example (x : Option Nat) : x = none ∨ ∃ n, x = some n := by
  grind only [cases Option]

example (x : Option Nat) : x = none ∨ ∃ n, x = some n := by
  grind [cases Option] => cases #b20c <;> instantiate only [#80cc]
