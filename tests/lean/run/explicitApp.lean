/-!
# Tests for app elaborator in explicit mode
-/

namespace Test1

/-!
Named arguments in explicit mode should not cause arguments they depend on to become implicit,
unless there are no more positional arguments.
-/

theorem foo {p : Prop} [Decidable p] (h : ite p x y = x) : p := sorry

variable {p : Prop} [Decidable p] {α : Type} (x y : α) (h : ite p x y = x)


example : p := @foo (h := h)

example : p := @foo (h := h) _ _ _ _ _

/--
error: function expected at
  foo h
term has type
  p
-/
#guard_msgs in
example : p := @foo (h := h) _ _ _ _ _ _

end Test1
