/-!
# Warn when a `@[deprecated]` attribute points at an already-deprecated declaration

When `A` is deprecated in favor of `B`, and `B` is itself deprecated in favor of `C`, deprecating
`A` towards `B` is discouraged: `B`'s deprecation record points at `C`, so `A` should point at `C`
instead. The `@[deprecated]` attribute inspects `B`'s deprecation record (only one step) and warns
accordingly. The check can be turned off with `linter.deprecated.deprecatedTarget`.
-/

set_option linter.deprecated true

def c1 : Nat := 0

@[deprecated c1 (since := "2020-01-01")]
def b1 : Nat := 0

/--
warning: `b1` is itself deprecated in favor of `c1`; consider deprecating `a1` in favor of `c1` instead

Note: This warning can be disabled with `set_option linter.deprecated.deprecatedTarget false`
-/
#guard_msgs in
@[deprecated b1 (since := "2020-01-01")]
def a1 : Nat := 0

/-! Longer chain `a2 → b2 → c2 → d2`: only one step is followed, so `a2` is pointed at `c2`. -/

def d2 : Nat := 0

set_option linter.deprecated false in
@[deprecated d2 (since := "2020-01-01")]
def c2 : Nat := 0

set_option linter.deprecated false in
@[deprecated c2 (since := "2020-01-01")]
def b2 : Nat := 0

/--
warning: `b2` is itself deprecated in favor of `c2`; consider deprecating `a2` in favor of `c2` instead

Note: This warning can be disabled with `set_option linter.deprecated.deprecatedTarget false`
-/
#guard_msgs in
@[deprecated b2 (since := "2020-01-01")]
def a2 : Nat := 0

/-! Text-only terminal: `b3` is deprecated without an explicit replacement. -/

@[deprecated "no replacement" (since := "2020-01-01")]
def b3 : Nat := 0

/--
warning: `b3` is itself deprecated, but without an explicit replacement; `a3` is being deprecated in favor of a deprecated declaration

Note: This warning can be disabled with `set_option linter.deprecated.deprecatedTarget false`
-/
#guard_msgs in
@[deprecated b3 (since := "2020-01-01")]
def a3 : Nat := 0

/-! One step at a target that is itself text-only deprecated: `a4` is pointed at `c4`. -/

@[deprecated "no replacement" (since := "2020-01-01")]
def c4 : Nat := 0

set_option linter.deprecated false in
@[deprecated c4 (since := "2020-01-01")]
def b4 : Nat := 0

/--
warning: `b4` is itself deprecated in favor of `c4`; consider deprecating `a4` in favor of `c4` instead

Note: This warning can be disabled with `set_option linter.deprecated.deprecatedTarget false`
-/
#guard_msgs in
@[deprecated b4 (since := "2020-01-01")]
def a4 : Nat := 0

/-! Type disagreement between the initial declaration and the suggested replacement. -/

def c5 : Bool := true

@[deprecated c5 (since := "2020-01-01")]
def b5 : Bool := true

/--
warning: `b5` is itself deprecated in favor of `c5`; consider deprecating `a5` in favor of `c5` instead

Note: The suggested replacement has a different type:
  Bool
instead of
  Nat

Note: This warning can be disabled with `set_option linter.deprecated.deprecatedTarget false`
-/
#guard_msgs in
@[deprecated b5 (since := "2020-01-01")]
def a5 : Nat := 0

/-! No warning when the target is not itself deprecated. -/

def c6 : Nat := 0

#guard_msgs in
@[deprecated c6 (since := "2020-01-01")]
def a6 : Nat := 0

/-! Disabling via `linter.deprecated.deprecatedTarget` suppresses the check. -/

def c8 : Nat := 0

@[deprecated c8 (since := "2020-01-01")]
def b8 : Nat := 0

set_option linter.deprecated.deprecatedTarget false in
#guard_msgs in
@[deprecated b8 (since := "2020-01-01")]
def a8 : Nat := 0

/-! Turning off `linter.deprecated` entirely also suppresses the check. -/

set_option linter.deprecated false in
#guard_msgs in
@[deprecated b8 (since := "2020-01-01")]
def a9 : Nat := 0
