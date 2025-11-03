import Lean.LibrarySuggestions.Default

/-!
# Test that set_library_suggestions can override the default

This test verifies that even after importing Default (which sets Sine Qua Non as the default),
we can override it with a different selector.
-/

-- First, verify the default is set by using it
example {x : Dyadic} {prec : Int} : x.roundDown prec ≤ x := by
  grind +suggestions

-- Now override with an empty selector
set_library_suggestions (fun _ _ => pure #[])

-- Verify that grind +suggestions now fails because the empty selector provides no suggestions
/--
error: `grind` failed
case grind
x : Dyadic
prec : Int
h : ¬x.roundDown prec ≤ x
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] ¬x.roundDown prec ≤ x
  [eqc] False propositions
    [prop] x.roundDown prec ≤ x
  [cutsat] Assignment satisfying linear constraints
    [assign] prec := 2
  [linarith] Linarith assignment for `Dyadic`
    [assign] x := -1
    [assign] x.roundDown prec := 0
-/
#guard_msgs in
example {x : Dyadic} {prec : Int} : x.roundDown prec ≤ x := by
  grind +suggestions
