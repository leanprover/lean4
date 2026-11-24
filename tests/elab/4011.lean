import Lean.LabelAttribute
/-!
# Using a label attribute in the file that registers it

Regression test for #4011: the error message should explain why a freshly registered attribute
is not yet available, instead of just reporting an unknown attribute.
-/
register_label_attr rom

/--
error: Unknown attribute `[rom]`: its syntax is declared, but its implementation is not available yet. Attributes registered with `initialize` or `register_label_attr` can only be used in modules that import the file declaring them.
-/
#guard_msgs in
@[rom] def womp : 2 + 2 = 4 := by rfl

/-- error: Unknown attribute `[nonexistent]` -/
#guard_msgs in
@[nonexistent] def womp' : 2 + 2 = 4 := by rfl
