import Lean.LibrarySuggestions.Basic

/--
error: No library suggestions engine registered. (Note that Lean does not provide a default library suggestions engine, these must be provided by a downstream library, and configured using `set_library_suggestions`.)
-/
#guard_msgs in
example : True := by
  grind +suggestions

set_library_suggestions (fun _ _ => pure #[])

#guard_msgs in
example : True := by
  grind +suggestions

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

set_library_suggestions (fun _ _ => pure #[{ name := `p, score := 1.0 }])

example : P 7 := by
  grind +suggestions

set_library_suggestions (fun _ _ => pure #[{ name := `List.append_assoc, score := 1.0 }])

-- Make sure there is no warning about the redundant theorem.
#guard_msgs in
example (x y z : List Nat) : x ++ (y ++ z) = (x ++ y) ++ z := by
  grind +suggestions

theorem f : True := trivial

set_library_suggestions (fun _ _ => pure #[{ name := `f, score := 1.0 }])

-- Make sure that bad suggestions (e.g. not patterns) from premise selection are dropped silently.
#guard_msgs in
example (x y z : List Nat) : x ++ (y ++ z) = (x ++ y) ++ z := by
  grind +suggestions
