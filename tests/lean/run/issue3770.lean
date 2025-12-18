macro "foo" : tactic => `(tactic|fail "first")
macro_rules | `(tactic|foo) => `(tactic|exact 1)
macro_rules | `(tactic|foo) => `(tactic|fail "middle")
macro_rules | `(tactic|foo) => `(tactic|exact 2)
macro_rules | `(tactic|foo) => `(tactic|fail "last")

def what_is_foo : Nat := by foo

/-- info: 2 -/
#guard_msgs in
#eval what_is_foo


macro "bar" : tactic => `(tactic|fail "first")
macro_rules | `(tactic|bar) => `(tactic|fail "middle")
macro_rules | `(tactic|bar) => `(tactic|fail "last")

/--
error: first
⊢ Nat
-/
#guard_msgs in
def what_is_bar : Nat := by bar
