import Lean.LibrarySuggestions.Basic
import Lean.Elab.Tactic.SolveByElim

-- First test without any library suggestions set up
/--
error: No library suggestions engine registered. (Add `import Lean.LibrarySuggestions.Default` to use Lean's built-in engine, or use `set_library_suggestions` to configure a custom one.)
-/
#guard_msgs in
example : True := by
  solve_by_elim +suggestions

-- Set up an empty library suggestion engine
set_library_suggestions (fun _ _ => pure #[])

#guard_msgs in
example : True := by
  solve_by_elim +suggestions

-- A custom proposition that solve_by_elim doesn't know about by default
-- We use a custom non-defeq type so that `trivial` and `rfl` don't solve it
inductive MyProp : Nat → Prop where
  | intro37 : MyProp 37
  | intro42 : MyProp 42

theorem myPropThm37 : MyProp 37 := MyProp.intro37

-- Without +suggestions (or explicit lemma), solve_by_elim should fail
-- Note: need -constructor to prevent constructor from solving it
/--
error: failed
-/
#guard_msgs in
example : MyProp 37 := by
  solve_by_elim -constructor

-- With explicit lemma, it works
example : MyProp 37 := by
  solve_by_elim only [myPropThm37]

-- Set up library suggestion engine that suggests our theorem
set_library_suggestions (fun _ _ => pure #[{ name := `myPropThm37, score := 1.0 }])

-- With +suggestions, it should work
example : MyProp 37 := by
  solve_by_elim -constructor +suggestions

-- Test that suggestions work with local hypotheses
example (h : MyProp 42) : MyProp 42 := by
  solve_by_elim +suggestions

-- Test with chain of applications
inductive IsZero : Nat → Prop where
  | intro : IsZero 0

def fromZero (n : Nat) (h : n = 0) : IsZero n := by
  subst h
  exact IsZero.intro

theorem isZero_zero : IsZero 0 := IsZero.intro

set_library_suggestions (fun _ _ => pure #[
  { name := `isZero_zero, score := 1.0 }
])

example : IsZero 0 := by
  solve_by_elim +suggestions

-- Test with bad suggestions - they should be ignored silently
set_library_suggestions (fun _ _ => pure #[
  { name := `isZero_zero, score := 1.0 },
  { name := `nonexistent_theorem, score := 0.5 }
])

-- Bad suggestions should be filtered out, and the good one should work
example : IsZero 0 := by
  solve_by_elim +suggestions
