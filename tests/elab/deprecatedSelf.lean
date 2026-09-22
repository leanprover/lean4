/-!
Tests that a `@[deprecated]` attribute whose replacement is the annotated declaration
itself is rejected as an error.
-/

/--
error: Invalid `[deprecated]` attribute: `foo` cannot be deprecated in favor of itself
-/
#guard_msgs in
@[deprecated foo (since := "2026-07-09")]
def foo := 1

def bar := 1

/--
error: Invalid `[deprecated]` attribute: `bar` cannot be deprecated in favor of itself
-/
#guard_msgs in
attribute [deprecated bar (since := "2026-07-09")] bar

-- Deprecating in favor of a different declaration still works.
def baz := 1

@[deprecated baz (since := "2026-07-09")]
def oldBaz := 1

namespace A

/-- error: Invalid `[deprecated]` attribute: `A.a` cannot be deprecated in favor of itself -/
#guard_msgs in
@[deprecated A.a (since := "2026-07-09")]
def a := 1

/-- error: Invalid `[deprecated]` attribute: `A.b` cannot be deprecated in favor of itself -/
#guard_msgs in
@[deprecated b (since := "2026-07-09")]
def b := 1

end A
