axiom testSorry : α

opaque a : Nat
opaque b : Nat
def c := a
@[irreducible] def d := a
opaque P : Nat → Prop


/--
error: not a `rfl`-theorem: the left-hand side
  a
is not definitionally equal to the right-hand side
  b
-/
#guard_msgs in
@[rfl] theorem a_eq_b : a = b := testSorry
theorem a_eq_c : a = c := rfl
@[rfl] theorem a_eq_c' : a = c := Eq.refl _
theorem a_eq_c'' : a = c := Eq.refl _
@[rfl] theorem a_eq_d : a = d := by simp [d]

/-- error: not a `rfl`-theorem: the conculsion should be an equality, but is True -/
#guard_msgs in
@[rfl] def not_an_eq : True := trivial


def Tricky.rfl := a_eq_b
/--
error: not a `rfl`-theorem: the left-hand side
  a
is not definitionally equal to the right-hand side
  b
-/
#guard_msgs in
theorem Tricky.a_eq_b : a = b := rfl -- to confuse the heuristics

/-- error: dsimp made no progress -/
#guard_msgs in example (h : P b) : P a := by dsimp [a_eq_b]; exact h

/-- error: dsimp made no progress -/
#guard_msgs in example (h : P b) : P a := by dsimp [Tricky.a_eq_b]; exact h

#guard_msgs in example (h : P c) : P a := by dsimp [a_eq_c]; exact h

#guard_msgs in example (h : P c) : P a := by dsimp [a_eq_c']; exact h

/-- error: dsimp made no progress -/
#guard_msgs in example (h : P c) : P a := by dsimp [a_eq_c'']; exact h

#guard_msgs in example (h : P d) : P a := by dsimp [a_eq_d]; exact h
