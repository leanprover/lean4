/-! Check that non-predicate inductives that do not support large elimination are rejected -/

set_option bootstrap.inductiveCheckResultingUniverse false

/-- error: (kernel) non-predicate inductive types must support large elimination -/
#guard_msgs in
inductive Wrap (α : Sort u) : Sort u
  | wrap (unwrap : α)

/-- error: (kernel) non-predicate inductive types must support large elimination -/
#guard_msgs in
inductive POption (α : Sort u) : Sort u
  | none
  | some (val : α)
