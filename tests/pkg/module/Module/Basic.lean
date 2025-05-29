module

axiom testSorry : α

/-! Module docstring -/

/-- A definition (not exposed). -/
def f := 1
/-- An definition (exposed) -/
@[expose] def fexp := 1

/-- A theorem. -/
theorem t : f = 1 := testSorry

-- Check that the theorem types are checked in exported context, where `f` is not defeq to `1`
-- (but `fexp` is)

/--
error: type mismatch
  y
has type
  Vector Unit 1 : Type
but is expected to have type
  Vector Unit f : Type
-/
#guard_msgs in
theorem v (x : Vector Unit f) (y : Vector Unit 1) : x = y := testSorry

/--
error: type mismatch
  y
has type
  Vector Unit 1 : Type
but is expected to have type
  Vector Unit f : Type
-/
#guard_msgs in
private theorem v' (x : Vector Unit f) (y : Vector Unit 1) : x = y := testSorry -- TODO: Should this not be allowed?

private theorem v'' (x : Vector Unit fexp) (y : Vector Unit 1) : x = y := testSorry

-- Check that rfl theorems are complained about if they aren't rfl in the context of their type

/--
error: Not a definitional equality: the left-hand side
  f
is not definitionally equal to the right-hand side
  1

Note: This theorem is exported from the current module. This requires that all definitions that need to be unfolded to prove this theorem must be exposed.
-/
#guard_msgs in
theorem trfl : f = 1 := rfl
/-- error: unknown attribute [rfl] -/
#guard_msgs in
@[rfl] theorem trfl' : f = 1 := (rfl)

-- TODO: Should these not be all allowed?
/--
error: Not a definitional equality: the left-hand side
  f
is not definitionally equal to the right-hand side
  1

Note: This theorem is exported from the current module. This requires that all definitions that need to be unfolded to prove this theorem must be exposed.
-/
#guard_msgs in
private theorem trflprivate : f = 1 := rfl
private def trflprivate' : f = 1 := rfl
@[defeq] private def trflprivate''' : f = 1 := rfl
/--
error: Not a definitional equality: the left-hand side
  f
is not definitionally equal to the right-hand side
  1

Note: This theorem is exported from the current module. This requires that all definitions that need to be unfolded to prove this theorem must be exposed.
-/
#guard_msgs in
@[defeq] private theorem trflprivate'''' : f = 1 := (rfl)

theorem fexp_trfl : fexp = 1 := rfl
@[defeq] theorem fexp_trfl' : fexp = 1 := rfl

opaque P : Nat → Prop
axiom hP1 : P 1

/-- error: dsimp made no progress -/
#guard_msgs in
example : P f := by dsimp only [t]; exact hP1
example : P f := by simp only [t]; exact hP1

/-- error: dsimp made no progress -/
#guard_msgs in
example : P f := by dsimp only [trfl]; exact hP1
/-- error: dsimp made no progress -/
#guard_msgs in
example : P f := by dsimp only [trfl']; exact hP1

/-- error: dsimp made no progress -/
#guard_msgs in
example : P f := by dsimp only [trflprivate]; exact hP1
example : P f := by dsimp only [trflprivate']; exact hP1


example : P fexp := by dsimp only [fexp_trfl]; exact hP1
example : P fexp := by dsimp only [fexp_trfl]; exact hP1


-- Check that the error message does not mention the export issue if
-- it wouldn’t be a rfl otherwise either

/--
error: Not a definitional equality: the left-hand side
  f
is not definitionally equal to the right-hand side
  2
-/
#guard_msgs in
@[defeq] theorem not_rfl : f = 2 := testSorry
