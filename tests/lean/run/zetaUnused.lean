
/--
info: b : Bool
⊢ if b = true then
    let_fun unused := ();
    True
  else False
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example (b : Bool) : if b then have unused := (); True else False := by
  trace_state; sorry

/--
info: b : Bool
⊢ b = true
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example (b : Bool) : if b then have unused := (); True else False := by
  simp; trace_state; sorry

/--
info: b : Bool
⊢ b = true ∧
    let_fun unused := ();
    True
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example (b : Bool) : if b then have unused := (); True else False := by
  simp (config := Lean.Meta.Simp.neutralConfig); trace_state; sorry

/-- error: simp made no progress -/
#guard_msgs in
example (b : Bool) : if b then have unused := (); True else False := by
  simp (config := Lean.Meta.Simp.neutralConfig) only; trace_state; sorry

/--
info: b : Bool
⊢ if b = true then True else False
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example (b : Bool) : if b then have unused := (); True else False := by
  simp (config := Lean.Meta.Simp.neutralConfig) +zeta only; trace_state; sorry


/--
info: b : Bool
⊢ if b = true then True else False
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example (b : Bool) : if b then have unused := (); True else False := by
  simp (config := Lean.Meta.Simp.neutralConfig) +zetaUnused only; trace_state; sorry


-- Before the introduction of zetaUnused, split would do collateral damage to unused letFuns.
-- Now they are preserved:

/--
info: case isTrue
b : Bool
h✝ : b = true
⊢ let_fun unused := ();
  True
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example (b : Bool) : if b then have unused := (); True else False := by
  split
  · trace_state; sorry
  · sorry
