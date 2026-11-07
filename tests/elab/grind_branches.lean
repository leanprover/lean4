/-!
Tests the `branches` threshold, which bounds the number of branches created by case-splits in the
search tree, and the deprecated `splits` option.
-/

/-! A wide disjunction: each case is refuted at once, so a case-split on each disjunct creates a
single branch. -/

example (x : Int)
    (h : x ≤ 0 ∨ 100 ≤ x ∨ x = 2 ∨ x = 4 ∨ x = 6 ∨ x = 8 ∨ x = 10 ∨ x = 12 ∨ x = 14 ∨ x = 16 ∨ x = 18 ∨ x = 20 ∨ x = 22 ∨ x = 24 ∨ x = 26 ∨ x = 28 ∨ x = 30 ∨ x = 32 ∨ x = 34 ∨ x = 36)
    (h₁ : 0 < x) (h₂ : x < 100) (h₃ : x % 2 = 1) : False := by
  grind

example (x : Int)
    (h : x ≤ 0 ∨ 100 ≤ x ∨ x = 2 ∨ x = 4 ∨ x = 6 ∨ x = 8 ∨ x = 10 ∨ x = 12 ∨ x = 14 ∨ x = 16 ∨ x = 18 ∨ x = 20 ∨ x = 22 ∨ x = 24 ∨ x = 26 ∨ x = 28 ∨ x = 30 ∨ x = 32 ∨ x = 34 ∨ x = 36)
    (h₁ : 0 < x) (h₂ : x < 100) (h₃ : x % 2 = 1) : False := by
  grind (branches := 17)

/--
error: `grind` has failed after reaching the threshold `(branches := 16)`, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
example (x : Int)
    (h : x ≤ 0 ∨ 100 ≤ x ∨ x = 2 ∨ x = 4 ∨ x = 6 ∨ x = 8 ∨ x = 10 ∨ x = 12 ∨ x = 14 ∨ x = 16 ∨ x = 18 ∨ x = 20 ∨ x = 22 ∨ x = 24 ∨ x = 26 ∨ x = 28 ∨ x = 30 ∨ x = 32 ∨ x = 34 ∨ x = 36)
    (h₁ : 0 < x) (h₂ : x < 100) (h₃ : x % 2 = 1) : False := by
  grind (branches := 16)

/-! Independent case-splits: `2³ - 1` branches. -/

example (x y z : Int) (c₁ c₂ c₃ : Bool) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    (if c₁ then x else 0) + (if c₂ then y else 0) + (if c₃ then z else 0) ≤ x + y + z := by
  lia (branches := 7)

/--
error: `lia` has failed after reaching the threshold `(branches := 6)`, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
example (x y z : Int) (c₁ c₂ c₃ : Bool) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    (if c₁ then x else 0) + (if c₂ then y else 0) + (if c₃ then z else 0) ≤ x + y + z := by
  lia (branches := 6)

/-! The case-splits on `rᵢ ∨ sᵢ` and `¬b ∨ ¬u ∨ ¬v` are irrelevant in the first case of `a ∨ b`.
Non-chronological backtracking skips their second cases, which are not counted afterwards, so the
case-splits in the second case of `a ∨ b` stay within the threshold. -/

example (a b p q u v r₁ s₁ r₂ s₂ r₃ s₃ : Prop)
    (_ : ¬a ∨ p ∨ q) (_ : ¬a ∨ ¬p ∨ q) (_ : ¬a ∨ p ∨ ¬q) (_ : ¬a ∨ ¬p ∨ ¬q)
    (_ : ¬b ∨ u ∨ v) (_ : ¬b ∨ ¬u ∨ v) (_ : ¬b ∨ u ∨ ¬v) (_ : ¬b ∨ ¬u ∨ ¬v)
    (_ : r₁ ∨ s₁) (_ : r₂ ∨ s₂) (_ : r₃ ∨ s₃)
    (_ : a ∨ b) : False := by
  grind (branches := 6)

/--
error: `grind` has failed after reaching the threshold `(branches := 5)`, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
example (a b p q u v r₁ s₁ r₂ s₂ r₃ s₃ : Prop)
    (_ : ¬a ∨ p ∨ q) (_ : ¬a ∨ ¬p ∨ q) (_ : ¬a ∨ p ∨ ¬q) (_ : ¬a ∨ ¬p ∨ ¬q)
    (_ : ¬b ∨ u ∨ v) (_ : ¬b ∨ ¬u ∨ v) (_ : ¬b ∨ u ∨ ¬v) (_ : ¬b ∨ ¬u ∨ ¬v)
    (_ : r₁ ∨ s₁) (_ : r₂ ∨ s₂) (_ : r₃ ∨ s₃)
    (_ : a ∨ b) : False := by
  grind (branches := 5)

/-! Each `finish` has its own threshold. Here, each `finish` needs 3 branches, and the case-split
performed by `cases_next` is not counted. -/

example (x y : Int) (hx : x = 1 ∨ x = 3 ∨ x = 5) (hy : y = 1 ∨ y = 3 ∨ y = 5)
    (h : x % 2 = 0 ∨ y % 2 = 0) : False := by
  grind (branches := 3) =>
    cases_next <;> finish

/--
error: `finish` has failed after reaching the threshold `(branches := 2)`, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
example (x y : Int) (hx : x = 1 ∨ x = 3 ∨ x = 5) (hy : y = 1 ∨ y = 3 ∨ y = 5)
    (h : x % 2 = 0 ∨ y % 2 = 0) : False := by
  grind (branches := 2) =>
    cases_next <;> finish

/-! `splits` is deprecated and ignored, except that `splits := 0` disables case-splits. -/

/--
warning: `splits` has been deprecated, use `branches` instead

Note: This linter can be disabled with `set_option linter.deprecated false`
-/
#guard_msgs in
set_option linter.deprecated true in
example (x : Int)
    (h : x ≤ 0 ∨ 100 ≤ x ∨ x = 2 ∨ x = 4 ∨ x = 6 ∨ x = 8 ∨ x = 10 ∨ x = 12 ∨ x = 14 ∨ x = 16 ∨ x = 18 ∨ x = 20 ∨ x = 22 ∨ x = 24 ∨ x = 26 ∨ x = 28 ∨ x = 30 ∨ x = 32 ∨ x = 34 ∨ x = 36)
    (h₁ : 0 < x) (h₂ : x < 100) (h₃ : x % 2 = 1) : False := by
  grind (splits := 3)

/--
warning: `splits` has been deprecated, use `branches` instead

Note: This linter can be disabled with `set_option linter.deprecated false`
---
error: `grind` has failed after reaching the threshold `(branches := 0)`, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
set_option linter.deprecated true in
example (x : Int) (h : x = 1 ∨ x = 3) (h₁ : x % 2 = 0) : False := by
  grind (splits := 0)

/--
warning: `splits` has been deprecated, use `branches` instead

Note: This linter can be disabled with `set_option linter.deprecated false`
-/
#guard_msgs in
set_option linter.deprecated true in
example (x : Int) (h : x = 1 ∨ x = 3) (h₁ : x % 2 = 0) : False := by
  grind => finish (splits := 2)

-- No warning: the default value.
#guard_msgs in
set_option linter.deprecated true in
example (x : Int) (h : x = 1 ∨ x = 3) (h₁ : x % 2 = 0) : False := by
  grind (splits := 9)
