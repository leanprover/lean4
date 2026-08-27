/-!
# Tests for `with_unfolding_none` tactic

The `.none` transparency mode prevents unfolding of all definitions, including reducible ones.
This is stricter than `.reducible`, which unfolds `@[reducible]` definitions.
-/

-- A reducible definition: unfolded by `.reducible` but not by `.none`
@[reducible] def myId (x : Nat) : Nat := x

-- Default transparency can see through myId
example : myId 42 = 42 := by rfl

-- with_unfolding_none blocks even reducible definitions
/--
error: Tactic `rfl` failed: The left-hand side
  myId 42
is not definitionally equal to the right-hand side
  42

⊢ myId 42 = 42
-/
#guard_msgs in
example : myId 42 = 42 := by
  with_unfolding_none rfl
