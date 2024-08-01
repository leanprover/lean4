/-!
# Tests of the `in` command combinator
-/

/-!
Testing that some commands shouldn't be on the RHS of `in`.
-/

/-- warning: unexpected 'open' in this context, only has local effect -/
#guard_msgs in
set_option pp.all true in open Lean

/-- warning: unexpected 'variable' in this context, only has local effect -/
#guard_msgs in
set_option pp.all true in variable (n : Nat)

/-- warning: unexpected 'universe' in this context, only has local effect -/
#guard_msgs in
set_option pp.all true in universe u


namespace issue_4743
/-!
Testing that local attributes shouldn't be on the RHS of `in`.
https://github.com/leanprover/lean4/issues/4743

Now there is a warning on `local simp`
-/

axiom falso : False

/--
warning: unexpected non-global attribute, local and scoped attributes do not have the expected effect in this context
-/
#guard_msgs in
set_option trace.debug true in
attribute [local simp] falso

end issue_4743


/-!
Testing that namespaced declarations with local attributes shouldn't be on the RHS of `in`.
https://github.com/leanprover/lean4/issues/4744

Now there is a warning on `local simp`
-/

/--
warning: unexpected non-global attribute, local and scoped attributes do not have the expected effect in this context
-/
#guard_msgs in
@[local simp]
axiom Foo.falso : False
