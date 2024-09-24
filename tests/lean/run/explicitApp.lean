/-!
# Tests for app elaborator in explicit mode
-/

namespace Test1

/-!
Named arguments in explicit mode should not cause arguments they depend on to become implicit,
except when doing error recovery.
-/

theorem foo {p : Prop} [Decidable p] (h : ite p x y = x) : p := sorry

variable {p : Prop} [Decidable p] {α : Type} (x y : α) (h : ite p x y = x)


/--
error: insufficient number of arguments, 5 missing explicit argument(s) are dependencies of
a named argument and must be provided. Typically each missing argument can be filled in with '_' or `(_)`.
In explicit mode, `_` for an instance argument triggers typeclass synthesis and `(_)` does not.

These are the inferred missing arguments:
  α
  x
  y
  p
  inst✝
-/
#guard_msgs in example : p := @foo (h := h)

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
