set_option simp.rfl.checkTransparency true

-- `myId` is at default transparency, not reducible
def myId (n : Nat) : Nat := n

-- LHS `myId n` and RHS `n` are only defeq if `myId` is unfolded (requires default transparency)
/--
warning: `myId_eq` is a `[defeq]` simp theorem, but its left-hand side
  myId n
is not definitionally equal to the right-hand side
  n
at `.implicit` transparency. Possible solutions:
1- use `(rfl)` as the proof
2- mark constants occurring in the lhs and rhs as `[implicit_reducible]`
-/
#guard_msgs in
@[simp] theorem myId_eq (n : Nat) : myId n = n := rfl

#guard_msgs in
@[simp] theorem myId_eq' (n : Nat) : myId n = n := (rfl)

attribute [instance_reducible] myId

#guard_msgs in
@[simp] theorem myId_eq'' (n : Nat) : myId n = n := rfl


-- `implicit_reducible` version should be fine
@[instance_reducible] def myId2 (n : Nat) : Nat := n

#guard_msgs in
@[simp] theorem myId2_eq (n : Nat) : myId2 n = n := rfl

/--
warning: `add_zero` is a `[defeq]` simp theorem, but its left-hand side
  n + 0
is not definitionally equal to the right-hand side
  n
at `.implicit` transparency. Possible solutions:
1- use `(rfl)` as the proof
2- mark constants occurring in the lhs and rhs as `[implicit_reducible]`
-/
#guard_msgs in
@[simp] theorem add_zero (n : Nat) : n + 0 = n := rfl

#guard_msgs in
@[simp] theorem add_zero' (n : Nat) : n + 0 = n := (rfl)


section Config

/-
There was a bug that the `simp.rfl.checkTransparency` linter would check
`LHS =?= RHS` at `.implicit` as expected, but with `proj := .no` config instead of `.yesWithDelta`.
This led to a linter warning even though LHS and RHS are implicit-reducibly defeq.
-/

structure S where f : Nat → Nat

@[implicit_reducible] def mkS : S := ⟨fun n => n⟩

set_option simp.rfl.checkTransparency true

#guard_msgs in
@[simp, defeq] theorem mkS_f (n : Nat) : mkS.f n = n := rfl

end Config
