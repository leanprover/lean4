import Lean.PremiseSelection.Basic

/--
error: No premise selector registered. (Note that Lean does not provide a default premise selector, these must be provided by a downstream library, and configured using `set_premise_selector`.)
-/
#guard_msgs in
example : True := by
  grind +premises

set_premise_selector (fun _ _ => pure #[])

#guard_msgs in
example : True := by
  grind +premises

def P (_ : Nat) := True
theorem p : P 7 := trivial

/--
error: `grind` failed
case grind
h : ¬P 37
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] ¬P 37
  [eqc] False propositions
    [prop] P 37
-/
#guard_msgs in
example : P 37 := by
  grind

example : P 7 := by
  grind [p]

set_premise_selector (fun _ _ => pure #[{ name := `p, score := 1.0 }])

example : P 7 := by
  grind +premises
