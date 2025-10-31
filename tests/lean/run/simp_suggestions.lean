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

-- Test that simp +suggestions (without ?) gives a helpful error
/--
error: +suggestions requires using simp? instead of simp
-/
#guard_msgs in
example (a b : Nat) : myCustomAdd a b = myCustomAdd b a := by
  simp +suggestions
  sorry

-- Test that simp_all? +suggestions works on the goal
/--
info: Try this:
  [apply] simp_all only [myCustomAdd_comm]
-/
#guard_msgs in
example (a b : Nat) : myCustomAdd a b = myCustomAdd b a := by
  simp_all? +suggestions

-- Test that simp_all? +suggestions works on a hypothesis
/--
info: Try this:
  [apply] simp_all only [myCustomAdd_comm]
-/
#guard_msgs in
example (a b c : Nat) (h : myCustomAdd a b = c) : myCustomAdd b a = c := by
  simp_all? +suggestions

-- Test that simp_all +suggestions (without ?) gives a helpful error
/--
error: +suggestions requires using simp_all? instead of simp_all
-/
#guard_msgs in
example (a b : Nat) (h : myCustomAdd a b = myCustomAdd b a) : myCustomAdd a b = myCustomAdd b a := by
  simp_all +suggestions
  sorry
