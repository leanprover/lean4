import Lean.PremiseSelection

-- A custom function that simp doesn't know about
def myCustomAdd (x y : Nat) : Nat := x + y

-- A helper lemma about our custom function
theorem myCustomAdd_comm (x y : Nat) : myCustomAdd x y = myCustomAdd y x := by
  simp [myCustomAdd, Nat.add_comm]

-- Set up a premise selector that suggests our helper theorem
set_premise_selector (fun _ _ => pure #[{ name := `myCustomAdd_comm, score := 1.0 }])

-- Test that regular simp? fails without the premise
example (a b : Nat) : myCustomAdd a b = myCustomAdd b a := by
  fail_if_success simp?
  exact myCustomAdd_comm a b

-- Test that simp? +suggestions succeeds by using the selected premise
/--
info: Try this:
  [apply] simp only [myCustomAdd_comm]
-/
#guard_msgs in
example (a b : Nat) : myCustomAdd a b = myCustomAdd b a := by
  simp? +suggestions
