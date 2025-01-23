

-- Before the introduction of zetaUnused, split would do collateral damage to unused letFuns.
-- Now they are preserved:

/--
warning: declaration uses 'sorry'
---
info: case isTrue
b : Bool
h✝ : b = true
⊢ let_fun unused := ();
  True
-/
#guard_msgs in
example (b : Bool) : if b then have unused := (); True else False := by
  split
  · trace_state
    sorry
  · sorry
