module

/-! Tests anchor ordinal references (e.g., `#c726/2`) used by the `cases` tactic in `grind` scripts.
Distinct case-split candidates may have identical anchors (e.g., when they differ only in
shadowed variables with the same name), and ordinal references are used to disambiguate them.
See issue #13877. Hidden variables (e.g., `x✝`) are distinguished by their rank, so they do not
need ordinal references. See issue #15778. -/

opaque f : Nat → Nat

-- `h1` and `h2` have identical anchors: they differ only in the shadowed `x`.
-- `cases?` disambiguates them using ordinal references.
/--
info: Try these:
  [apply] cases #c726 for
    ∃ z, f z = x
  [apply] cases #c726/2 for
    ∃ z, f z = x✝
-/
#guard_msgs (info) in
example : ∀ x y, (∃ z, f z = x) → (∃ z, f z = y) → (∀ z, f z ≠ y) → False := by
  intro x x h1 h2 h3
  grind =>
    cases?
    cases #c726
    instantiate only [#1256]

/--
info: Try these:
  [apply] grind only [#c726, #1256]
  [apply] grind only
  [apply] grind => cases #c726 <;> instantiate only [#1256]
-/
#guard_msgs (info) in
example : ∀ x y, (∃ z, f z = x) → (∃ z, f z = y) → (∀ z, f z ≠ y) → False := by
  intro x x h1 h2 h3
  grind?

-- Explicit ordinal reference: split `h1`'s existential (the second match), then `h2`'s
-- (which becomes the first remaining match).
example : ∀ x y, (∃ z, f z = x) → (∃ z, f z = y) → (∀ z, f z ≠ y) → False := by
  intro x x h1 h2 h3
  grind =>
    cases #c726/2
    cases #c726
    instantiate only [#1256]

-- Out-of-range ordinal.
/--
error: `cases` tactic failed, invalid anchor
-/
#guard_msgs (error) in
example : ∀ x y, (∃ z, f z = x) → (∃ z, f z = y) → (∀ z, f z ≠ y) → False := by
  intro x x h1 h2 h3
  grind =>
    cases #c726/3

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
