module

/-! Tests anchor ordinal references (e.g., `#7b48/2`) used by the `cases` tactic in `grind` scripts.
Distinct case-split candidates that differ only in inaccessible variables have identical
anchors, and ordinal references are used to disambiguate them. See issue #13877. -/

opaque f : Nat → Nat

-- `h1` and `h2` have identical anchors: they differ only in the inaccessible `x✝`/`y✝`.
-- `cases?` disambiguates them using ordinal references.
/--
info: Try these:
  [apply] cases #7b48 for
    ∃ z, f z = y✝
  [apply] cases #7b48/2 for
    ∃ z, f z = x✝
-/
#guard_msgs (info) in
example : ∀ x y, (∃ z, f z = x) → (∃ z, f z = y) → (∀ z, f z ≠ y) → False := by
  intro _ _ h1 h2 h3
  grind =>
    cases?
    cases #7b48
    instantiate only [#5976]

/--
info: Try these:
  [apply] grind only [#7b48, #5976]
  [apply] grind only
  [apply] grind => cases #7b48 <;> instantiate only [#5976]
-/
#guard_msgs (info) in
example : ∀ x y, (∃ z, f z = x) → (∃ z, f z = y) → (∀ z, f z ≠ y) → False := by
  intro _ _ h1 h2 h3
  grind?

-- Explicit ordinal reference: split `h1`'s existential (the second match), then `h2`'s
-- (which becomes the first remaining match).
example : ∀ x y, (∃ z, f z = x) → (∃ z, f z = y) → (∀ z, f z ≠ y) → False := by
  intro _ _ h1 h2 h3
  grind =>
    cases #7b48/2
    cases #7b48
    instantiate only [#5976]

-- Out-of-range ordinal.
/--
error: `cases` tactic failed, invalid anchor
-/
#guard_msgs (error) in
example : ∀ x y, (∃ z, f z = x) → (∃ z, f z = y) → (∀ z, f z ≠ y) → False := by
  intro _ _ h1 h2 h3
  grind =>
    cases #7b48/3
