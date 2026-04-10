set_option simp.rfl.checkTransparency true

-- `myId` is at default transparency, not reducible
def myId (n : Nat) : Nat := n

-- LHS `myId n` and RHS `n` are only defeq if `myId` is unfolded (requires default transparency)
/--
warning: `myId_eq` is a `[defeq]` simp theorem, but its left-hand side
  myId n
is not definitionally equal to the right-hand side
  n
at `.instances` transparency. Possible solutions:
1- use `(rfl)` as the proof
2- mark constants occurring in the lhs and rhs as `[implicit_reducible]`
-/
#guard_msgs in
@[simp] theorem myId_eq (n : Nat) : myId n = n := rfl

#guard_msgs in
@[simp] theorem myId_eq' (n : Nat) : myId n = n := (rfl)

attribute [implicit_reducible] myId

#guard_msgs in
@[simp] theorem myId_eq'' (n : Nat) : myId n = n := rfl


-- `implicit_reducible` version should be fine
@[implicit_reducible] def myId2 (n : Nat) : Nat := n

#guard_msgs in
@[simp] theorem myId2_eq (n : Nat) : myId2 n = n := rfl

/--
warning: `add_zero` is a `[defeq]` simp theorem, but its left-hand side
  n + 0
is not definitionally equal to the right-hand side
  n
at `.instances` transparency. Possible solutions:
1- use `(rfl)` as the proof
2- mark constants occurring in the lhs and rhs as `[implicit_reducible]`
-/
#guard_msgs in
@[simp] theorem add_zero (n : Nat) : n + 0 = n := rfl

#guard_msgs in
@[simp] theorem add_zero' (n : Nat) : n + 0 = n := (rfl)
