axiom testSorry : α

opaque a : Nat
opaque b : Nat
def c := a -- non-reducible: `a = c` only at default transparency
@[reducible] def c' := a -- reducible: `a = c'` holds at instance transparency
@[irreducible] def d := a
opaque P : Nat → Prop

@[irreducible] def ac := a = c
@[irreducible] def ac' := a = c'

/--
error: Not a definitional equality at instance transparency: the left-hand side
  a
is not definitionally equal to the right-hand side
  b
at the transparency used by `dsimp`
-/
#guard_msgs in
@[defeq] theorem a_eq_b : a = b := testSorry
theorem a_eq_c : a = c := rfl -- not auto-tagged
/--
error: Not a definitional equality at instance transparency: the left-hand side
  a
is not definitionally equal to the right-hand side
  c
at the transparency used by `dsimp`

Note: The equality holds at default/all transparency. Use `@[backward_defeq]` instead, or rewrite the proof so that the equality holds at instance transparency.
-/
#guard_msgs in
@[defeq] theorem a_eq_c' : a = c := Eq.refl _
@[backward_defeq] theorem a_eq_c'' : a = c := Eq.refl _

@[defeq] theorem a_eq_c''' : a = c' := Eq.refl _
/--
error: Not a definitional equality at instance transparency: the left-hand side
  a
is not definitionally equal to the right-hand side
  c
at the transparency used by `dsimp`

Note: The equality holds at default/all transparency. Use `@[backward_defeq]` instead, or rewrite the proof so that the equality holds at instance transparency.
-/
#guard_msgs in
@[defeq] theorem a_eq_c'''' : ac := by with_unfolding_all rfl
@[backward_defeq] theorem a_eq_c''''' : ac := by with_unfolding_all rfl
/--
error: Not a definitional equality at instance transparency: the left-hand side
  a
is not definitionally equal to the right-hand side
  d
at the transparency used by `dsimp`

Note: The equality holds at default/all transparency. Use `@[backward_defeq]` instead, or rewrite the proof so that the equality holds at instance transparency.
-/
#guard_msgs in
@[defeq] theorem a_eq_d : a = d := by simp [d]
@[backward_defeq] theorem a_eq_d' : a = d := by simp [d]

/-- error: Not a definitional equality: the conclusion should be an equality, but is `True` -/
#guard_msgs in
@[defeq] def not_an_eq : True := trivial


def Tricky.rfl := a_eq_b
/--
error: Not a definitional equality: the left-hand side
  a
is not definitionally equal to the right-hand side
  b
-/
#guard_msgs in
theorem Tricky.a_eq_b : a = b := rfl -- to confuse the heuristics; auto-tagged `[backward_defeq]`

/-! Does `#print` show the attribute? -/

/-- info: @[defeq] theorem a_eq_c''' : a = c' -/
#guard_msgs in
#print sig a_eq_c'''

/-! Does dsimp use `[defeq]`? -/

/-- error: `dsimp` made no progress -/
#guard_msgs in example (h : P b) : P a := by dsimp [a_eq_b]; exact h

/-- error: `dsimp` made no progress -/
#guard_msgs in example (h : P b) : P a := by dsimp [Tricky.a_eq_b]; exact h

/-- error: `dsimp` made no progress -/
#guard_msgs in example (h : P c) : P a := by dsimp [a_eq_c]; exact h

#guard_msgs in example (h : P c') : P a := by dsimp [a_eq_c''']; exact h

/-- error: `dsimp` made no progress -/
#guard_msgs in example (h : P c) : P a := by dsimp [a_eq_c'']; exact h

set_option backward.defeqAttrib.useBackward true in
#guard_msgs in example (h : P c) : P a := by dsimp [a_eq_c'']; exact h

-- Order of simp and defeq attribute
def e1 := a -- not reducible, so `[defeq]` would fail strict
@[simp] theorem e1_eq_a : e1 = a := rfl
/-- error: `dsimp` made no progress -/
#guard_msgs in example (h : P a) : P e1 := by dsimp; exact h
set_option backward.defeqAttrib.useBackward true in
#guard_msgs in example (h : P a) : P e1 := by dsimp; exact h

@[reducible] def e2 := a
@[defeq, simp] theorem e2_eq_a : e2 = a := (rfl)
#guard_msgs in example (h : P a) : P e2 := by dsimp; exact h

@[reducible] def e3 := a
@[defeq, simp] theorem e3_eq_a : e3 = a := (rfl) -- defeq before simp also works
#guard_msgs in example (h : P a) : P e3 := by dsimp; exact h

-- Tests the `defeq` attribute on a realized constant: That they are set, and that they
-- are transported out
def f := a
#guard_msgs in example (h : P a) : P f := by dsimp [f]; exact h
-- `f.eq_1` etc. are only `[backward_defeq]` (not `[defeq]`) since `f` is semireducible;
-- so we need to opt into the backward behavior for `dsimp` to use them.
set_option backward.defeqAttrib.useBackward true in
#guard_msgs in example (h : P a) : P f := by dsimp [f.eq_1]; exact h
set_option backward.defeqAttrib.useBackward true in
#guard_msgs in example (h : P a) : P f := by dsimp [f.eq_def]; exact h
set_option backward.defeqAttrib.useBackward true in
#guard_msgs in example (h : P a) : P f := by dsimp [f.eq_unfold]; exact h


def Q := 1 = 1
@[defeq, simp] theorem Q_true : Q := rfl
/-- error: `dsimp` made no progress -/
#guard_msgs in example : Q := by dsimp [Q_true]
