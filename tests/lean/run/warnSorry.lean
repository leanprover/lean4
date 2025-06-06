import Lean
/-!
# `warn.sorry` tests

When `warn.sorry` is false, don't log the "declaration uses 'sorry'" warning.
-/

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
example : True := sorry

#guard_msgs in
set_option warn.sorry false in
example : True := sorry

elab "synth_sorry" : term <= expectedType => Lean.Meta.mkSorry expectedType true

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
example : True := synth_sorry

/-- error: declaration has unlogged elaboration errors (please report this issue) -/
#guard_msgs in
set_option warn.sorry false in
example : True := synth_sorry
