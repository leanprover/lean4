axiom testSorry : α

opaque a : Nat
opaque b : Nat
def c := a
@[irreducible] def d := a
opaque P : Nat → Prop

@[irreducible] def ac := a = c

/--
error: Not a definitional equality: the left-hand side
  a
is not definitionally equal to the right-hand side
  b
-/
#guard_msgs in
@[defeq] theorem a_eq_b : a = b := testSorry
theorem a_eq_c : a = c := rfl
@[defeq] theorem a_eq_c' : a = c := Eq.refl _
theorem a_eq_c'' : a = c := Eq.refl _
@[defeq] theorem a_eq_c''' : ac := by with_unfolding_all rfl
@[defeq] theorem a_eq_d : a = d := by simp [d]

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
theorem Tricky.a_eq_b : a = b := rfl -- to confuse the heuristics

/-! Does `#print` show the attribute? -/

/-- info: @[defeq] theorem a_eq_c : a = c -/
#guard_msgs in
#print sig a_eq_c

/-! Does dsimp use it? -/

/-- error: `dsimp` made no progress -/
#guard_msgs in example (h : P b) : P a := by dsimp [a_eq_b]; exact h

/-- error: `dsimp` made no progress -/
#guard_msgs in example (h : P b) : P a := by dsimp [Tricky.a_eq_b]; exact h

#guard_msgs in example (h : P c) : P a := by dsimp [a_eq_c]; exact h

#guard_msgs in example (h : P c) : P a := by dsimp [a_eq_c']; exact h

/-- error: `dsimp` made no progress -/
#guard_msgs in example (h : P c) : P a := by dsimp [a_eq_c'']; exact h

-- a_eq_c''' is correctly tagged, but not used by `a_eq_c` because simp does not look through `ac`.
/-- error: `dsimp` made no progress -/
#guard_msgs in example (h : P c) : P a := by dsimp [a_eq_c''']; exact h

#guard_msgs in example (h : P d) : P a := by dsimp [a_eq_d]; exact h

-- Order of simp and rfl attribute
def e1 := a
@[simp] theorem e1_eq_a : e1 = a := rfl
#guard_msgs in example (h : P a) : P e1 := by dsimp; exact h

def e2 := a
@[defeq,simp] theorem e2_eq_a : e2 = a := (rfl)
#guard_msgs in example (h : P a) : P e2 := by dsimp; exact h

def e3 := a
@[simp,defeq] theorem e3_eq_a : e2 = a := (rfl) -- defeq has to come before simp
/-- error: `dsimp` made no progress -/
#guard_msgs in example (h : P a) : P e3 := by dsimp; exact h

-- Tests the `defeq` attribute on a realized constant: That they are set, and that they
-- are transported out
def f := a
#guard_msgs in example (h : P a) : P f := by dsimp [f]; exact h
#guard_msgs in example (h : P a) : P f := by dsimp [f.eq_1]; exact h
#guard_msgs in example (h : P a) : P f := by dsimp [f.eq_def]; exact h
#guard_msgs in example (h : P a) : P f := by dsimp [f.eq_unfold]; exact h


def Q := 1 = 1
@[defeq, simp] theorem Q_true : Q := rfl
/-- error: `dsimp` made no progress -/
#guard_msgs in example : Q := by dsimp [Q_true]
