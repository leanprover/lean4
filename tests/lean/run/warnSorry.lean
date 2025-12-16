import Lean
/-!
# `warn.sorry` tests

When `warn.sorry` is false, don't log the "declaration uses `sorry`" warning.
-/

/-- warning: declaration uses `sorry` -/
#guard_msgs in
example : True := sorry

#guard_msgs in
set_option warn.sorry false in
example : True := sorry

/-!
Synthetic sorries should come with associated errors.
We want to get an error if there is a synthetic sorry with no associated error.
However: sometimes there are synthetic sorries in terms that come from other other terms
that have already been warned about. There is no way to tell if a given synthetic sorry had
been reported on previously. We want to be able to turn off the warning in this case too.
If we can tell whether sorries have already been warned about,
we could direct the user to inform us about elaboration bugs (synthetic sorries with no errors in the message log).

So, for now we report them just like a user `sorry`.
-/

elab "synth_sorry" : term <= expectedType => Lean.Meta.mkSorry expectedType true

/-- warning: declaration uses `sorry` -/
#guard_msgs in
example : True := synth_sorry

#guard_msgs in
set_option warn.sorry false in
example : True := synth_sorry
