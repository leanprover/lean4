module

/-! Tests anchor ordinal references (e.g., `#d151/2`) used by the `cases` tactic in `grind` scripts.
Distinct case-split candidates may have identical anchors (e.g., when they differ only in
implicit arguments), and ordinal references are used to disambiguate them. See issue #13877.
Local variables are distinguished by their anchors, even when they are hidden (e.g., `x✝`) or
shadowed, so they do not need ordinal references. See issues #15778 and #16033. -/

opaque f : Nat → Nat
opaque g {α : Type} : Nat

-- `h1` and `h2` have identical anchors: they differ only in the implicit argument of `g`.
-- `cases?` disambiguates them using ordinal references.
/--
info: Try these:
  [apply] cases #d151 for
    ∃ z, f z = g
  [apply] cases #d151/2 for
    ∃ z, f z = g
-/
#guard_msgs (info) in
example : (∃ z, f z = @g Nat) → (∃ z, f z = @g Int) → (∀ z, f z ≠ @g Int) → False := by
  intro h1 h2 h3
  grind =>
    cases?
    cases #d151
    instantiate only [#09e6]

/--
info: Try these:
  [apply] grind only [#d151, #09e6]
  [apply] grind only
  [apply] grind => cases #d151 <;> instantiate only [#09e6]
-/
#guard_msgs (info) in
example : (∃ z, f z = @g Nat) → (∃ z, f z = @g Int) → (∀ z, f z ≠ @g Int) → False := by
  intro h1 h2 h3
  grind?

-- Explicit ordinal reference: split `h1`'s existential (the second match), then `h2`'s
-- (which becomes the first remaining match).
example : (∃ z, f z = @g Nat) → (∃ z, f z = @g Int) → (∀ z, f z ≠ @g Int) → False := by
  intro h1 h2 h3
  grind =>
    cases #d151/2
    cases #d151
    instantiate only [#09e6]

-- Out-of-range ordinal.
/--
error: `cases` tactic failed, invalid anchor
-/
#guard_msgs (error) in
example : (∃ z, f z = @g Nat) → (∃ z, f z = @g Int) → (∀ z, f z ≠ @g Int) → False := by
  intro h1 h2 h3
  grind =>
    cases #d151/3

-- The shadowed `x✝` and the visible `x` have distinct anchors.
/--
info: Try these:
  [apply] cases #fb4b for
    ∃ z, f z = x
  [apply] cases #cbd2 for
    ∃ z, f z = x✝
-/
#guard_msgs (info) in
example : ∀ x y, (∃ z, f z = x) → (∃ z, f z = y) → (∀ z, f z ≠ y) → False := by
  intro x x h1 h2 h3
  grind =>
    cases?
    cases #fb4b
    instantiate only [#9900]

-- Hidden variables `x✝` and `y✝` have distinct anchors.
/--
info: Try these:
  [apply] cases #b82e for
    ∃ z, f z = y✝
  [apply] cases #cbd2 for
    ∃ z, f z = x✝
-/
#guard_msgs (info) in
example : ∀ x y, (∃ z, f z = x) → (∃ z, f z = y) → (∀ z, f z ≠ y) → False := by
  intro _ _ h1 h2 h3
  grind =>
    cases?
    cases #b82e
    instantiate only [#6b62]
