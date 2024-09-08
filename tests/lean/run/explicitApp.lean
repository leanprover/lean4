/-!
# Tests for app elaborator in explicit mode
-/

namespace Test1

/-!
Named arguments in explicit mode cause arguments it depends on to become implicit.
However, inst implicit arguments had odd behavior with `_`, since supplying `_` would override
the fact that it should be implicit.
-/

theorem foo {p : Prop} [Decidable p] (h : ite p x y = x) : p := sorry

variable {p : Prop} [Decidable p] {α : Type} (x y : α) (h : ite p x y = x)

example : p := @foo (h := h)
/--
error: function expected at
  foo h
term has type
  p
-/
#guard_msgs in
example : p := @foo (h := h) _

end Test1
